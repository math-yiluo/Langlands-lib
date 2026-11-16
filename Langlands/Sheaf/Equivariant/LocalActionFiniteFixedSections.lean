import Langlands.Sheaf.Equivariant.LocalAction
import Mathlib.Algebra.Module.Submodule.Lattice

noncomputable section

namespace Langlands.Sheaf.Equivariant

open CategoryTheory Opposite

universe v u uG uA vA wA uR w uI

variable {T : Type u} [Category.{v} T]
variable {G : Type uG} [Group G] [TopologicalSpace G]

section Concrete

variable {A : Type uA} [Category.{vA} A] {FA : A → A → Type*} {CA : A → Type wA}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{wA} A FA]

/-- One open subgroup below a prescribed bound and all acting subgroups,
fixing a supplied family of sections. -/
structure CommonFixedSections (F : Tᵒᵖ ⥤ A) {I : Type uI} (U : I → T)
    (H : I → OpenSubgroup G) (a : ∀ i, (H i : Subgroup G) →* (End (U i))ᵐᵒᵖ)
    (s : ∀ i, ToType (F.obj (op (U i)))) (Q : OpenSubgroup G) where
  subgroup : OpenSubgroup G
  le_bound : subgroup ≤ Q
  le_action : ∀ i, subgroup ≤ H i
  fixes : ∀ i (h : (H i : Subgroup G)), (h : G) ∈ subgroup →
    F.map (a i h).unop.op (s i) = s i

/-- Finitely many discrete sections can be fixed simultaneously, below any
prescribed open subgroup. -/
theorem nonempty_commonFixedSections (F : Tᵒᵖ ⥤ A) {I : Type uI} [Finite I]
    (U : I → T) (H : I → OpenSubgroup G)
    (a : ∀ i, (H i : Subgroup G) →* (End (U i))ᵐᵒᵖ)
    (s : ∀ i, ToType (F.obj (op (U i))))
    (hs : ∀ i, IsDiscreteSection F (a i) (s i)) (Q : OpenSubgroup G) :
    Nonempty (CommonFixedSections F U H a s Q) := by
  classical
  choose N hNH hN using hs
  let M : OpenSubgroup G := Q ⊓ OpenSubgroup.iInfOfFinite N
  have hMN (i : I) : M ≤ N i :=
    inf_le_right.trans (OpenSubgroup.iInfOfFinite_le N i)
  exact ⟨{
    subgroup := M
    le_bound := inf_le_left
    le_action := fun i => (hMN i).trans (hNH i)
    fixes := fun i h hh => hN i h (hMN i hh)
  }⟩

/-- Common fixing data for a finite family of sections of a discrete presheaf
at admissible local actions. -/
def LocalActionSystem.commonFixedSections (L : LocalActionSystem T G)
    (F : Tᵒᵖ ⥤ A) (hF : L.IsDiscrete F) {I : Type uI} [Finite I]
    (U : I → T) (H : I → OpenSubgroup G)
    (a : ∀ i, (H i : Subgroup G) →* (End (U i))ᵐᵒᵖ)
    (ha : ∀ i, L.IsAdmissible (U i) (H i) (a i))
    (s : ∀ i, ToType (F.obj (op (U i)))) (Q : OpenSubgroup G) :
    CommonFixedSections F U H a s Q :=
  Classical.choice (nonempty_commonFixedSections F U H a s
    (fun i => hF _ _ _ (ha i) (s i)) Q)

/-- A strictly intertwining arrow preserves fixedness on the same subgroup. -/
theorem fixed_restrict_of_intertwines (F : Tᵒᵖ ⥤ A)
    {U V : T} {H H' N : OpenSubgroup G}
    {a : (H : Subgroup G) →* (End U)ᵐᵒᵖ}
    {b : (H' : Subgroup G) →* (End V)ᵐᵒᵖ}
    {p : V ⟶ U} (hNH : N ≤ H) (hNH' : N ≤ H')
    (hp : ∀ (g : G) (hg : g ∈ N),
      (b ⟨g, hNH' hg⟩).unop ≫ p = p ≫ (a ⟨g, hNH hg⟩).unop)
    {s : ToType (F.obj (op U))}
    (hs : ∀ h : (H : Subgroup G), (h : G) ∈ N → F.map (a h).unop.op s = s) :
    ∀ h : (H' : Subgroup G), (h : G) ∈ N →
      F.map (b h).unop.op (F.map p.op s) = F.map p.op s := by
  intro h hh
  calc
    F.map (b h).unop.op (F.map p.op s) =
        F.map ((b h).unop ≫ p).op s := by
      rw [op_comp, F.map_comp, CategoryTheory.comp_apply]
    _ = F.map (p ≫ (a ⟨h, hNH hh⟩).unop).op s := by rw [hp h hh]
    _ = F.map p.op (F.map (a ⟨h, hNH hh⟩).unop.op s) := by
      rw [op_comp, F.map_comp, CategoryTheory.comp_apply]
    _ = F.map p.op s := congrArg (F.map p.op) (hs _ hh)

end Concrete

section Modules

variable {R : Type uR} [CommRing R]
variable (F : Tᵒᵖ ⥤ ModuleCat.{w} R) {I : Type uI} {U : I → T}
variable {H : I → OpenSubgroup G}
variable (a : ∀ i, (H i : Subgroup G) →* (End (U i))ᵐᵒᵖ)

/-- Families fixed by the elements of `N` belonging to each acting subgroup.
For a common acting subgroup these are the simultaneous fixed families. -/
def fixedFamilySubmodule (N : OpenSubgroup G) :
    Submodule R (∀ i, F.obj (op (U i))) where
  carrier s := ∀ i (h : (H i : Subgroup G)), (h : G) ∈ N →
    F.map (a i h).unop.op (s i) = s i
  zero_mem' := fun _ _ _ => map_zero _
  add_mem' := by
    intro s t hs ht i h hh
    change F.map (a i h).unop.op (s i + t i) = s i + t i
    rw [map_add, hs i h hh, ht i h hh]
  smul_mem' := by
    intro r s hs i h hh
    change F.map (a i h).unop.op (r • s i) = r • s i
    rw [map_smul, hs i h hh]

@[simp]
theorem mem_fixedFamilySubmodule (N : OpenSubgroup G) (s : ∀ i, F.obj (op (U i))) :
    s ∈ fixedFamilySubmodule F a N ↔
      ∀ i (h : (H i : Subgroup G)), (h : G) ∈ N →
        F.map (a i h).unop.op (s i) = s i := Iff.rfl

/-- Shrinking the fixing subgroup enlarges the fixed-family submodule. -/
theorem fixedFamilySubmodule_antitone {M N : OpenSubgroup G} (hMN : M ≤ N) :
    fixedFamilySubmodule F a N ≤ fixedFamilySubmodule F a M :=
  fun _ hs i h hh => hs i h (hMN hh)

/-- Open subgroups contained in a prescribed bound and every acting subgroup. -/
abbrev CommonOpenSubgroup (Q : OpenSubgroup G) (H : I → OpenSubgroup G) :=
  {N : OpenSubgroup G // N ≤ Q ∧ ∀ i, N ≤ H i}

/-- Fixed-family submodules form a directed family under subgroup shrinking. -/
theorem directed_fixedFamilySubmodule (Q : OpenSubgroup G) :
    Directed (· ≤ ·) (fun N : CommonOpenSubgroup Q H =>
      fixedFamilySubmodule F a N.val) := by
  intro M N
  refine ⟨⟨M.val ⊓ N.val, inf_le_left.trans M.property.1,
    fun i => inf_le_left.trans (M.property.2 i)⟩, ?_, ?_⟩
  · exact fixedFamilySubmodule_antitone F a inf_le_left
  · exact fixedFamilySubmodule_antitone F a inf_le_right

/-- A finite family of discrete sections belongs to one common fixed-family
submodule, even with a prescribed upper bound on the subgroup. -/
theorem exists_mem_fixedFamilySubmodule [Finite I]
    (s : ∀ i, F.obj (op (U i)))
    (hs : ∀ i, IsDiscreteSection F (a i) (s i)) (Q : OpenSubgroup G) :
    ∃ N : CommonOpenSubgroup Q H, s ∈ fixedFamilySubmodule F a N.val := by
  obtain ⟨d⟩ := nonempty_commonFixedSections F U H a s hs Q
  exact ⟨⟨d.subgroup, d.le_bound, d.le_action⟩, d.fixes⟩

/-- The directed family of simultaneous fixed submodules exhausts the product
of the section modules at finitely many admissible local actions. -/
theorem LocalActionSystem.iSup_fixedFamilySubmodule (L : LocalActionSystem T G)
    [Finite I] (hF : L.IsDiscrete F)
    (ha : ∀ i, L.IsAdmissible (U i) (H i) (a i)) (Q : OpenSubgroup G) :
    (⨆ N : CommonOpenSubgroup Q H, fixedFamilySubmodule F a N.val) = ⊤ := by
  apply top_unique
  intro s _
  obtain ⟨N, hN⟩ := exists_mem_fixedFamilySubmodule F a s
    (fun i => hF _ _ _ (ha i) (s i)) Q
  exact Submodule.mem_iSup_of_mem N hN

end Modules

end Langlands.Sheaf.Equivariant
