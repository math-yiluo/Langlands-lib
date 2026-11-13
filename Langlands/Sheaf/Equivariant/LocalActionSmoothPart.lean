import Langlands.Sheaf.Equivariant.LocalActionDiscretePart

/-!
# The locally discrete part of a sheaf for a local action system

For a local action system on a site, a sheaf is locally discrete when every
section is, on a covering sieve, the restriction of discrete sections over
objects carrying admissible local actions. This has the shape of the
characterization of étale `G`-sheaves in Berkovich's remark after Definition
1.4.1. Assume that arrows between objects with admissible
local actions restrict discreteness, and that every cone over a cospan is
covered by objects with admissible local actions mapping to the cospan. Then the
locally discrete sections of a module sheaf form a subsheaf, the locally
discrete part. It is right adjoint to the inclusion of locally discrete sheaves;
locally discrete module sheaves form an abelian category with exact inclusion
and with enough injectives when all module sheaves have enough injectives.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject

universe v u uG uR w

variable {T : Type u} [Category.{v} T] {G : Type uG} [Group G] [TopologicalSpace G]

section Restriction

/-- An arrow `p : V ⟶ U` restricts discreteness from a local action `a` of `H`
on `U` to a local action `b` of `H'` on `V` when, for every open subgroup `K` of
`H`, a smaller open subgroup `M` of `H'` acts compatibly through elements of
`K`: for `h ∈ M` there is `k ∈ K` with `b h` followed by `p` equal to `p`
followed by `a k`. -/
def IsRestrictionEquivariant {U V : T} {H H' : OpenSubgroup G}
    (a : (H : Subgroup G) →* (End U)ᵐᵒᵖ) (b : (H' : Subgroup G) →* (End V)ᵐᵒᵖ)
    (p : V ⟶ U) : Prop :=
  ∀ K : OpenSubgroup G, K ≤ H → ∃ M : OpenSubgroup G, M ≤ H' ∧
    ∀ h : (H' : Subgroup G), (h : G) ∈ M → ∃ k : (H : Subgroup G), (k : G) ∈ K ∧
      (b h).unop ≫ p = p ≫ (a k).unop

/-- An arrow intertwining two local actions on a common open subgroup restricts
discreteness. -/
theorem isRestrictionEquivariant_of_intertwines {U V : T} {H H' : OpenSubgroup G}
    {a : (H : Subgroup G) →* (End U)ᵐᵒᵖ} {b : (H' : Subgroup G) →* (End V)ᵐᵒᵖ}
    {p : V ⟶ U} (N : OpenSubgroup G) (hNH : N ≤ H) (hNH' : N ≤ H')
    (hp : ∀ (g : G) (hg : g ∈ N), (b ⟨g, hNH' hg⟩).unop ≫ p = p ≫ (a ⟨g, hNH hg⟩).unop) :
    IsRestrictionEquivariant a b p := by
  intro K _
  refine ⟨N ⊓ K, inf_le_left.trans hNH', fun h hh => ?_⟩
  obtain ⟨hhN, hhK⟩ := OpenSubgroup.mem_inf.1 hh
  exact ⟨⟨h, hNH hhN⟩, hhK, hp h hhN⟩

variable {A : Type*} [Category A] {FA : A → A → Type*} {CA : A → Type*}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]

/-- Restriction of a section along two arrows is restriction along their
composite. -/
theorem map_op_comp_apply (F : Tᵒᵖ ⥤ A) {X Y Z : T} (x : X ⟶ Y) (y : Y ⟶ Z)
    (s : ToType (F.obj (op Z))) : F.map (x ≫ y).op s = F.map x.op (F.map y.op s) := by
  rw [op_comp, F.map_comp, CategoryTheory.comp_apply]

/-- Discreteness restricts along an arrow which restricts discreteness. -/
theorem IsDiscreteSection.restrict {F : Tᵒᵖ ⥤ A} {U V : T} {H H' : OpenSubgroup G}
    {a : (H : Subgroup G) →* (End U)ᵐᵒᵖ} {b : (H' : Subgroup G) →* (End V)ᵐᵒᵖ}
    {p : V ⟶ U} (hp : IsRestrictionEquivariant a b p) {s : ToType (F.obj (op U))}
    (hs : IsDiscreteSection F a s) : IsDiscreteSection F b (F.map p.op s) := by
  obtain ⟨K, hKH, hK⟩ := hs
  obtain ⟨M, hMH', hM⟩ := hp K hKH
  refine ⟨M, hMH', fun h hh => ?_⟩
  obtain ⟨k, hkK, hk⟩ := hM h hh
  rw [← map_op_comp_apply, hk, map_op_comp_apply, hK k hkK]

end Restriction

namespace LocalActionSystem

variable (L : LocalActionSystem T G) (J : GrothendieckTopology T)

/-- Given a cospan `f₁ : V₁ ⟶ U`, `f₂ : V₂ ⟶ U` and a cone `k₁ : W ⟶ V₁`,
`k₂ : W ⟶ V₂` over it, the sieve of arrows `e : W' ⟶ W` for which `e ≫ k₁` and
`e ≫ k₂` factor through one object `V` with an admissible local action, by an
arrow `W' ⟶ V` followed by arrows `p₁ : V ⟶ V₁` and `p₂ : V ⟶ V₂` forming a cone
over the cospan. -/
def fiberRefinementSieve {U V₁ V₂ W : T} (f₁ : V₁ ⟶ U) (f₂ : V₂ ⟶ U) (k₁ : W ⟶ V₁)
    (k₂ : W ⟶ V₂) : Sieve W where
  arrows W' e := ∃ (V : T) (H : OpenSubgroup G) (b : (H : Subgroup G) →* (End V)ᵐᵒᵖ)
    (k : W' ⟶ V) (p₁ : V ⟶ V₁) (p₂ : V ⟶ V₂), L.IsAdmissible V H b ∧
      p₁ ≫ f₁ = p₂ ≫ f₂ ∧ k ≫ p₁ = e ≫ k₁ ∧ k ≫ p₂ = e ≫ k₂
  downward_closed := by
    rintro W' W'' e ⟨V, H, b, k, p₁, p₂, hb, hp, h₁, h₂⟩ e'
    exact ⟨V, H, b, e' ≫ k, p₁, p₂, hb, hp, by simp only [Category.assoc, h₁],
      by simp only [Category.assoc, h₂]⟩

/-- The hypothesis for the locally discrete part. Every arrow between objects with
admissible local actions restricts discreteness (an abstract form of the
uniqueness of lifted actions in Berkovich's Key Lemma), and every cone over a
cospan is covered by objects with admissible local actions mapping to the
cospan (an abstract form of covering fibre products by distinguished étale
objects). -/
class HasAdmissibleRefinements : Prop where
  isRestrictionEquivariant : ∀ ⦃V V' : T⦄ ⦃H H' : OpenSubgroup G⦄
    ⦃a : (H : Subgroup G) →* (End V)ᵐᵒᵖ⦄ ⦃a' : (H' : Subgroup G) →* (End V')ᵐᵒᵖ⦄,
    L.IsAdmissible V H a → L.IsAdmissible V' H' a' → ∀ p : V' ⟶ V,
      IsRestrictionEquivariant a a' p
  fiberRefinementSieve_mem : ∀ ⦃U V₁ V₂ W : T⦄ (f₁ : V₁ ⟶ U) (f₂ : V₂ ⟶ U) (k₁ : W ⟶ V₁)
    (k₂ : W ⟶ V₂), k₁ ≫ f₁ = k₂ ≫ f₂ → L.fiberRefinementSieve f₁ f₂ k₁ k₂ ∈ J W

variable {L J}

/-- Objects with admissible local actions cover: apply the refinement hypothesis
to the cospan and cone of identities. -/
theorem HasAdmissibleRefinements.covers [L.HasAdmissibleRefinements J] : L.Covers J := by
  intro U
  refine J.superset_covering ?_
    (HasAdmissibleRefinements.fiberRefinementSieve_mem (L := L) (J := J) (𝟙 U) (𝟙 U) (𝟙 U) (𝟙 U) rfl)
  rintro W e ⟨V, H, b, k, p₁, -, hb, -, h₁, -⟩
  exact ⟨V, k, p₁, H, b, hb, by rw [h₁, Category.comp_id]⟩

variable {A : Type*} [Category A] {FA : A → A → Type*} {CA : A → Type*}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]

/-- Local discreteness of a section is stable under restriction. -/
theorem discreteSieve_map_mem [L.HasAdmissibleRefinements J] (F : Tᵒᵖ ⥤ A) {U U' : T}
    (g : U' ⟶ U) {s : ToType (F.obj (op U))} (hs : L.discreteSieve F s ∈ J U) :
    L.discreteSieve F (F.map g.op s) ∈ J U' := by
  refine J.transitive (J.pullback_stable g hs) _ ?_
  rintro W h ⟨V₁, k₁, f₁, H₁, a₁, ha₁, hs₁, hh⟩
  refine J.superset_covering ?_
    (HasAdmissibleRefinements.fiberRefinementSieve_mem (L := L) (J := J) f₁ g k₁ h hh)
  rintro W' e ⟨V, H, b, k, p₁, p₂, hb, hp, -, h₂⟩
  refine ⟨V, k, p₂, H, b, hb, ?_, h₂⟩
  rw [← map_op_comp_apply, ← hp, map_op_comp_apply]
  exact hs₁.restrict (HasAdmissibleRefinements.isRestrictionEquivariant (J := J) ha₁ hb p₁)

/-- Local discreteness of a section follows from local discreteness of two
sections, when on every object with an admissible local action, discreteness of
the restrictions of the two sections implies discreteness of the restriction of
the given one. The two discrete sieves are intersected, and each arrow of the
intersection is refined to a common object with an admissible local action. -/
theorem discreteSieve_mem_of_pair [L.HasAdmissibleRefinements J] {F₁ F₂ F : Tᵒᵖ ⥤ A} {U : T}
    {s₁ : ToType (F₁.obj (op U))} {s₂ : ToType (F₂.obj (op U))} {t : ToType (F.obj (op U))}
    (h₁ : L.discreteSieve F₁ s₁ ∈ J U) (h₂ : L.discreteSieve F₂ s₂ ∈ J U)
    (ht : ∀ (V : T) (H : OpenSubgroup G) (b : (H : Subgroup G) →* (End V)ᵐᵒᵖ),
      L.IsAdmissible V H b → ∀ f : V ⟶ U, IsDiscreteSection F₁ b (F₁.map f.op s₁) →
        IsDiscreteSection F₂ b (F₂.map f.op s₂) → IsDiscreteSection F b (F.map f.op t)) :
    L.discreteSieve F t ∈ J U := by
  refine J.transitive (J.intersection_covering h₁ h₂) _ ?_
  rintro W g ⟨⟨V₁, k₁, f₁, H₁, a₁, ha₁, hs₁, rfl⟩, ⟨V₂, k₂, f₂, H₂, a₂, ha₂, hs₂, hg⟩⟩
  refine J.superset_covering ?_
    (HasAdmissibleRefinements.fiberRefinementSieve_mem (L := L) (J := J) f₁ f₂ k₁ k₂ hg.symm)
  rintro W' e ⟨V, H, b, k, p₁, p₂, hb, hp, he₁, -⟩
  refine ⟨V, k, p₁ ≫ f₁, H, b, hb, ht V H b hb _ ?_ ?_, ?_⟩
  · rw [map_op_comp_apply]
    exact hs₁.restrict (HasAdmissibleRefinements.isRestrictionEquivariant (J := J) ha₁ hb p₁)
  · rw [hp, map_op_comp_apply]
    exact hs₂.restrict (HasAdmissibleRefinements.isRestrictionEquivariant (J := J) ha₂ hb p₂)
  · rw [← Category.assoc, he₁, Category.assoc]

end LocalActionSystem

namespace LocalActionSystem

variable (L : LocalActionSystem T G) (A : Type*) [Category A] {FA : A → A → Type*}
variable {CA : A → Type*} [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
variable (J : GrothendieckTopology T)

instance smoothSheafInclusion_full : (L.smoothSheafInclusion A J).Full :=
  inferInstanceAs (L.smoothSheafProperty A J).ι.Full

instance smoothSheafInclusion_faithful : (L.smoothSheafInclusion A J).Faithful :=
  inferInstanceAs (L.smoothSheafProperty A J).ι.Faithful

end LocalActionSystem

section Modules

variable {R : Type uR} [CommRing R]

section Pair

variable {J : GrothendieckTopology T}

/-- A section of a binary product of module sheaves is discrete for a local
action when its two projections are: a common open subgroup fixes both. -/
theorem isDiscreteSection_of_pair (D : Discrete WalkingPair ⥤ Sheaf J (ModuleCat.{w} R))
    [HasLimit D] {V : T} {H : OpenSubgroup G} {b : (H : Subgroup G) →* (End V)ᵐᵒᵖ}
    (x : (limit D).obj.obj (op V))
    (h₁ : IsDiscreteSection (D.obj ⟨.left⟩).obj b ((limit.π D ⟨.left⟩).hom.app (op V) x))
    (h₂ : IsDiscreteSection (D.obj ⟨.right⟩).obj b ((limit.π D ⟨.right⟩).hom.app (op V) x)) :
    IsDiscreteSection (limit D).obj b x := by
  obtain ⟨K₁, hK₁, h₁⟩ := h₁
  obtain ⟨K₂, -, h₂⟩ := h₂
  refine ⟨K₁ ⊓ K₂, inf_le_left.trans hK₁, fun h hh => ?_⟩
  apply sheaf_limit_sections_ext D
  rintro ⟨⟨⟩⟩
  · rw [NatTrans.naturality_apply]
    exact h₁ h (inf_le_left (a := K₁) hh)
  · rw [NatTrans.naturality_apply]
    exact h₂ h (inf_le_right (a := K₁) hh)

end Pair

namespace LocalActionSystem

variable (L : LocalActionSystem T G) (J : GrothendieckTopology T)
variable [L.HasAdmissibleRefinements J]

/-- The locally discrete sections: those whose discrete sieve is a covering
sieve. -/
def smoothSubmodule (F : Tᵒᵖ ⥤ ModuleCat.{w} R) (U : T) : Submodule R (F.obj (op U)) where
  carrier := {s | L.discreteSieve F s ∈ J U}
  add_mem' {s t} hs ht := LocalActionSystem.discreteSieve_mem_of_pair hs ht
    fun _ _ _ _ f h₁ h₂ => by
      rw [map_add]
      exact h₁.add h₂
  zero_mem' := by
    refine J.superset_covering ?_
      (LocalActionSystem.HasAdmissibleRefinements.covers (L := L) (J := J) U)
    rintro W g ⟨V, k, f, H, a, ha, rfl⟩
    refine ⟨V, k, f, H, a, ha, ?_, rfl⟩
    rw [map_zero]
    exact isDiscreteSection_zero F a
  smul_mem' r s hs := by
    refine J.superset_covering ?_ hs
    rintro W g ⟨V, k, f, H, a, ha, hs', rfl⟩
    refine ⟨V, k, f, H, a, ha, ?_, rfl⟩
    rw [map_smul]
    exact hs'.smul r

theorem mem_smoothSubmodule_iff {F : Tᵒᵖ ⥤ ModuleCat.{w} R} {U : T} (s : F.obj (op U)) :
    s ∈ smoothSubmodule L J F U ↔ L.discreteSieve F s ∈ J U :=
  Iff.rfl

/-- Restriction preserves the locally discrete submodules. -/
theorem map_mem_smoothSubmodule (F : Tᵒᵖ ⥤ ModuleCat.{w} R) {U U' : T} (g : U' ⟶ U)
    {s : F.obj (op U)} (hs : s ∈ smoothSubmodule L J F U) :
    F.map g.op s ∈ smoothSubmodule L J F U' :=
  LocalActionSystem.discreteSieve_map_mem F g hs

/-- Morphisms of presheaves preserve the locally discrete submodules. -/
theorem map_mem_smoothSubmodule_of_hom {F F' : Tᵒᵖ ⥤ ModuleCat.{w} R} (φ : F ⟶ F')
    {U : T} {s : F.obj (op U)} (hs : s ∈ smoothSubmodule L J F U) :
    φ.app (op U) s ∈ smoothSubmodule L J F' U :=
  J.superset_covering (L.discreteSieve_le_map φ s) hs

/-- A presheaf is locally discrete exactly when all its sections lie in the
locally discrete submodules. -/
theorem isLocallyDiscrete_iff_forall_mem (F : Tᵒᵖ ⥤ ModuleCat.{w} R) :
    L.IsLocallyDiscrete J F ↔ ∀ (U : T) (s : F.obj (op U)), s ∈ smoothSubmodule L J F U :=
  Iff.rfl

/-- Membership in the locally discrete submodules is local. -/
theorem mem_smoothSubmodule_of_covering {F : Tᵒᵖ ⥤ ModuleCat.{w} R} {U : T}
    (s : F.obj (op U)) {S : Sieve U} (hS : S ∈ J U)
    (h : ∀ ⦃W : T⦄ (g : W ⟶ U), S g → F.map g.op s ∈ smoothSubmodule L J F W) :
    s ∈ smoothSubmodule L J F U :=
  L.discreteSieve_mem_of_covering F s hS fun _ g hg => h g hg

/-- The presheaf of locally discrete parts. -/
def smoothPresheaf (F : Tᵒᵖ ⥤ ModuleCat.{w} R) : Tᵒᵖ ⥤ ModuleCat.{w} R where
  obj U := ModuleCat.of R (smoothSubmodule L J F U.unop)
  map {U V} f := ModuleCat.ofHom ((F.map f).hom.restrict fun _ hs =>
    map_mem_smoothSubmodule L J F f.unop hs)
  map_id U := by
    ext s
    simp
  map_comp f g := by
    ext s
    simp

/-- The inclusion of the locally discrete part. -/
def smoothPresheafι (F : Tᵒᵖ ⥤ ModuleCat.{w} R) : smoothPresheaf L J F ⟶ F where
  app U := ModuleCat.ofHom (smoothSubmodule L J F U.unop).subtype
  naturality _ _ _ := rfl

theorem smoothPresheafι_app_injective (F : Tᵒᵖ ⥤ ModuleCat.{w} R) (U : Tᵒᵖ) :
    Function.Injective ((smoothPresheafι L J F).app U) :=
  Subtype.val_injective

/-- Morphisms of presheaves restrict to the locally discrete parts. -/
def smoothPresheafMap {F F' : Tᵒᵖ ⥤ ModuleCat.{w} R} (φ : F ⟶ F') :
    smoothPresheaf L J F ⟶ smoothPresheaf L J F' where
  app U := ModuleCat.ofHom ((φ.app U).hom.restrict fun _ hs =>
    map_mem_smoothSubmodule_of_hom L J φ hs)
  naturality U V f := by
    ext s
    apply Subtype.ext
    exact congrArg (fun k => k.hom s.1) (φ.naturality f)

/-- The locally discrete part, functorially in the presheaf. -/
@[simps]
def smoothPresheafFunctor : (Tᵒᵖ ⥤ ModuleCat.{w} R) ⥤ (Tᵒᵖ ⥤ ModuleCat.{w} R) where
  obj := smoothPresheaf L J
  map := smoothPresheafMap L J
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The locally discrete part of a presheaf is locally discrete: its discrete
sieves are those of the ambient presheaf, since its inclusion is injective. -/
theorem isLocallyDiscrete_smoothPresheaf (F : Tᵒᵖ ⥤ ModuleCat.{w} R) :
    L.IsLocallyDiscrete J (smoothPresheaf L J F) := by
  intro U s
  rw [← L.discreteSieve_map_of_injective (smoothPresheafι L J F)
    (smoothPresheafι_app_injective L J F) s]
  exact s.2

variable {L J}

/-- The locally discrete part of a sheaf is a sheaf. A compatible family of maps
into the locally discrete parts glues in the ambient sheaf; every value of the
gluing has locally discrete restrictions along a covering sieve, so it is locally
discrete by locality. -/
theorem smoothPresheaf_isSheaf {F : Tᵒᵖ ⥤ ModuleCat.{w} R} (hF : Presheaf.IsSheaf J F) :
    Presheaf.IsSheaf J (smoothPresheaf L J F) := by
  intro E U S hS
  refine Presieve.IsSeparatedFor.isSheafFor (fun x t₁ t₂ h₁ h₂ => ?_) (fun x hx => ?_)
  · -- separatedness: compose with the injective inclusion
    have key : t₁ ≫ (smoothPresheafι L J F).app (op U) =
        t₂ ≫ (smoothPresheafι L J F).app (op U) := by
      apply hF.hom_ext ⟨S, hS⟩
      rintro ⟨W, g, hg⟩
      simp only [Category.assoc]
      rw [← (smoothPresheafι L J F).naturality]
      rw [← Category.assoc, ← Category.assoc]
      change (t₁ ≫ (smoothPresheaf L J F).map g.op) ≫ _ =
        (t₂ ≫ (smoothPresheaf L J F).map g.op) ≫ _
      rw [show t₁ ≫ (smoothPresheaf L J F).map g.op = x g hg from h₁ g hg,
        show t₂ ≫ (smoothPresheaf L J F).map g.op = x g hg from h₂ g hg]
    change (t₁ : E ⟶ (smoothPresheaf L J F).obj (op U)) = t₂
    refine ModuleCat.hom_ext (LinearMap.ext fun e => ?_)
    apply smoothPresheafι_app_injective L J F (op U)
    exact congrArg (fun φ => φ.hom e) key
  · -- existence: glue in the ambient sheaf and restrict the codomain
    let y : Presieve.FamilyOfElements (F ⋙ coyoneda.obj (op E)) S.arrows :=
      fun W g hg => x g hg ≫ (smoothPresheafι L J F).app (op W)
    have hy : y.Compatible := by
      intro W₁ W₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w
      change (x f₁ h₁ ≫ _) ≫ F.map g₁.op = (x f₂ h₂ ≫ _) ≫ F.map g₂.op
      rw [Category.assoc, Category.assoc, ← (smoothPresheafι L J F).naturality,
        ← (smoothPresheafι L J F).naturality, ← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ (smoothPresheafι L J F).app (op Z)) (hx g₁ g₂ h₁ h₂ w)
    let t := (hF E S hS).amalgamate y hy
    have ht : ∀ ⦃W : T⦄ (g : W ⟶ U) (hg : S g),
        t ≫ F.map g.op = x g hg ≫ (smoothPresheafι L J F).app (op W) :=
      fun W g hg => (hF E S hS).valid_glue hy g hg
    have hmem : ∀ e : E, t.hom e ∈ smoothSubmodule L J F U := fun e =>
      mem_smoothSubmodule_of_covering L J _ hS fun W g hg => by
        have := congrArg (fun φ => φ.hom e) (ht g hg)
        change (F.map g.op).hom (t.hom e) = ((x g hg).hom e).1 at this
        change (F.map g.op).hom (t.hom e) ∈ _
        rw [this]
        exact ((x g hg).hom e).2
    refine ⟨ModuleCat.ofHom (LinearMap.codRestrict _ t.hom hmem), fun W g hg => ?_⟩
    change ModuleCat.ofHom (LinearMap.codRestrict _ t.hom hmem) ≫
      (smoothPresheaf L J F).map g.op = x g hg
    refine ModuleCat.hom_ext (LinearMap.ext fun e => ?_)
    apply smoothPresheafι_app_injective L J F (op W)
    exact congrArg (fun φ => φ.hom e) (ht g hg)

variable (L J)

/-- The locally discrete subsheaf of a module sheaf. -/
def smoothSubsheafFunctor : Sheaf J (ModuleCat.{w} R) ⥤ Sheaf J (ModuleCat.{w} R) :=
  ObjectProperty.lift (Presheaf.IsSheaf J (A := ModuleCat.{w} R))
    (sheafToPresheaf J _ ⋙ smoothPresheafFunctor L J)
    fun F => smoothPresheaf_isSheaf F.property

/-- The inclusion of the locally discrete subsheaf. -/
def smoothSubsheafι : smoothSubsheafFunctor L J ⟶ 𝟭 (Sheaf J (ModuleCat.{w} R)) where
  app F := ObjectProperty.homMk (smoothPresheafι L J F.obj)
  naturality _ _ _ := rfl

theorem isLocallyDiscrete_smoothSubsheaf (F : Sheaf J (ModuleCat.{w} R)) :
    L.smoothSheafProperty (ModuleCat.{w} R) J ((smoothSubsheafFunctor L J).obj F) :=
  isLocallyDiscrete_smoothPresheaf L J F.obj

/-- The locally discrete part of a module sheaf, as a locally discrete sheaf. -/
def smoothCoreflector : Sheaf J (ModuleCat.{w} R) ⥤ L.SmoothSheaf (ModuleCat.{w} R) J :=
  (L.smoothSheafProperty (ModuleCat.{w} R) J).lift (smoothSubsheafFunctor L J)
    (isLocallyDiscrete_smoothSubsheaf L J)

variable {L J}

/-- A morphism from a locally discrete sheaf factors through the locally discrete
subsheaf. -/
def smoothLift {S F : Sheaf J (ModuleCat.{w} R)}
    (hS : L.smoothSheafProperty (ModuleCat.{w} R) J S) (f : S ⟶ F) :
    S ⟶ (smoothSubsheafFunctor L J).obj F :=
  ObjectProperty.homMk
    { app U := ModuleCat.ofHom (LinearMap.codRestrict _ (f.hom.app U).hom fun s =>
        map_mem_smoothSubmodule_of_hom L J f.hom (hS U.unop s))
      naturality U V g := by
        ext s
        apply Subtype.ext
        exact congrArg (fun k => k.hom s) (f.hom.naturality g) }

@[reassoc (attr := simp)]
theorem smoothLift_comp_ι {S F : Sheaf J (ModuleCat.{w} R)}
    (hS : L.smoothSheafProperty (ModuleCat.{w} R) J S) (f : S ⟶ F) :
    smoothLift hS f ≫ (smoothSubsheafι L J).app F = f :=
  rfl

variable (L J)

/-- The locally discrete part is right adjoint to the inclusion of locally
discrete sheaves. -/
def smoothAdjunction : L.smoothSheafInclusion (ModuleCat.{w} R) J ⊣ smoothCoreflector L J :=
  Adjunction.mkOfHomEquiv
    { homEquiv S F :=
        { toFun f := ObjectProperty.homMk (smoothLift S.property f)
          invFun g := g.hom ≫ (smoothSubsheafι L J).app F
          left_inv _ := rfl
          right_inv _ := rfl }
      homEquiv_naturality_left_symm _ _ := rfl
      homEquiv_naturality_right _ _ := rfl }

section AbelianStructure

variable [HasSheafify J (ModuleCat.{w} R)]

instance mono_smoothSubsheafι_app (F : Sheaf J (ModuleCat.{w} R)) :
    Mono ((smoothSubsheafι L J).app F) := by
  have : ∀ U, Mono ((smoothPresheafι L J F.obj).app U) := fun U =>
    (ModuleCat.mono_iff_injective _).2 (smoothPresheafι_app_injective L J F.obj U)
  have : Mono ((sheafToPresheaf J (ModuleCat.{w} R)).map ((smoothSubsheafι L J).app F)) :=
    NatTrans.mono_of_mono_app (smoothPresheafι L J F.obj)
  exact (sheafToPresheaf J (ModuleCat.{w} R)).mono_of_mono_map this

/-- A subsheaf of a locally discrete module sheaf is locally discrete. -/
instance smoothSheafProperty_isClosedUnderSubobjects :
    (L.smoothSheafProperty (ModuleCat.{w} R) J).IsClosedUnderSubobjects where
  prop_of_mono f _ hY :=
    LocalActionSystem.IsLocallyDiscrete.of_injective L f.hom (injective_app_of_mono f) hY

/-- A module sheaf whose locally discrete part is all of it is locally discrete. -/
theorem smoothSheafProperty_of_isIso {F : Sheaf J (ModuleCat.{w} R)}
    [IsIso ((smoothSubsheafι L J).app F)] : L.smoothSheafProperty (ModuleCat.{w} R) J F :=
  (L.smoothSheafProperty (ModuleCat.{w} R) J).prop_of_mono
    (inv ((smoothSubsheafι L J).app F)) (isLocallyDiscrete_smoothSubsheaf L J F)

/-- A quotient of a locally discrete module sheaf is locally discrete: an
epimorphism from a locally discrete sheaf factors through the locally discrete
subsheaf of its target, whose inclusion is then a monomorphism and an
epimorphism, hence an isomorphism. -/
instance smoothSheafProperty_isClosedUnderQuotients :
    (L.smoothSheafProperty (ModuleCat.{w} R) J).IsClosedUnderQuotients where
  prop_of_epi {X Y} f _ hX := by
    have hfac := smoothLift_comp_ι (L := L) (J := J) hX f
    have : Epi ((smoothSubsheafι L J).app Y) := epi_of_epi_fac hfac
    have : IsIso ((smoothSubsheafι L J).app Y) := isIso_of_mono_of_epi _
    exact smoothSheafProperty_of_isIso L J

/-- The zero module sheaf is locally discrete. -/
instance smoothSheafProperty_containsZero :
    (L.smoothSheafProperty (ModuleCat.{w} R) J).ContainsZero where
  exists_zero := by
    refine ⟨0, isZero_zero _, ?_⟩
    let f : (0 : Sheaf J (ModuleCat.{w} R)) ⟶ (smoothSubsheafFunctor L J).obj 0 := 0
    have : Mono f := ⟨fun g h _ => (isZero_zero _).eq_of_tgt g h⟩
    exact (L.smoothSheafProperty (ModuleCat.{w} R) J).prop_of_mono f
      (isLocallyDiscrete_smoothSubsheaf L J 0)

/-- A binary product of locally discrete module sheaves is locally discrete:
the two projections of a section are discrete over objects refining both discrete
sieves, so the section is discrete there. -/
instance smoothSheafProperty_isClosedUnderBinaryProducts :
    (L.smoothSheafProperty (ModuleCat.{w} R) J).IsClosedUnderBinaryProducts :=
  ObjectProperty.IsClosedUnderLimitsOfShape.mk' (by
    rintro _ ⟨D, hD⟩ U s
    refine LocalActionSystem.discreteSieve_mem_of_pair
      (hD ⟨.left⟩ U ((limit.π D ⟨.left⟩).hom.app (op U) s))
      (hD ⟨.right⟩ U ((limit.π D ⟨.right⟩).hom.app (op U) s))
      fun V H b _ f hl hr => isDiscreteSection_of_pair D _ ?_ ?_
    · rw [NatTrans.naturality_apply]
      exact hl
    · rw [NatTrans.naturality_apply]
      exact hr)

/-- Finite products of locally discrete module sheaves are locally discrete. -/
instance smoothSheafProperty_isClosedUnderFiniteProducts :
    (L.smoothSheafProperty (ModuleCat.{w} R) J).IsClosedUnderFiniteProducts :=
  ObjectProperty.IsClosedUnderFiniteProducts.mk'

/-- Locally discrete module sheaves form an abelian category. -/
instance smoothSheaf_abelian : Abelian (L.SmoothSheaf (ModuleCat.{w} R) J) :=
  inferInstance

/-- The inclusion of locally discrete sheaves preserves monomorphisms. -/
instance smoothSheafInclusion_preservesMonomorphisms :
    (L.smoothSheafInclusion (ModuleCat.{w} R) J).PreservesMonomorphisms :=
  ObjectProperty.preservesMonomorphisms_ι_of_isNormalEpiCategory
    (L.smoothSheafProperty (ModuleCat.{w} R) J)

/-- The inclusion of locally discrete sheaves preserves epimorphisms. -/
instance smoothSheafInclusion_preservesEpimorphisms :
    (L.smoothSheafInclusion (ModuleCat.{w} R) J).PreservesEpimorphisms :=
  ObjectProperty.preservesEpimorphisms_ι_of_isNormalMonoCategory
    (L.smoothSheafProperty (ModuleCat.{w} R) J)

/-- The inclusion of locally discrete sheaves preserves finite limits: kernels
of locally discrete sheaves are computed among all sheaves. -/
instance smoothSheafInclusion_preservesFiniteLimits :
    PreservesFiniteLimits (L.smoothSheafInclusion (ModuleCat.{w} R) J) :=
  have := (L.smoothSheafProperty (ModuleCat.{w} R) J).preservesKernels_ι
  Functor.preservesFiniteLimits_of_preservesKernels (L.smoothSheafProperty (ModuleCat.{w} R) J).ι

/-- The inclusion of locally discrete sheaves preserves finite colimits:
cokernels of locally discrete sheaves are computed among all sheaves. -/
instance smoothSheafInclusion_preservesFiniteColimits :
    PreservesFiniteColimits (L.smoothSheafInclusion (ModuleCat.{w} R) J) :=
  have := (L.smoothSheafProperty (ModuleCat.{w} R) J).preservesCokernels_ι
  Functor.preservesFiniteColimits_of_preservesCokernels (L.smoothSheafProperty (ModuleCat.{w} R) J).ι

/-- The locally discrete part of an injective module sheaf is injective among
locally discrete sheaves. -/
theorem injective_smoothCoreflector_obj (I : Sheaf J (ModuleCat.{w} R)) [Injective I] :
    Injective ((smoothCoreflector L J).obj I) :=
  (smoothAdjunction L J).map_injective I inferInstance

/-- Locally discrete module sheaves have enough injectives when module sheaves
do. -/
instance smoothSheaf_enoughInjectives [EnoughInjectives (Sheaf J (ModuleCat.{w} R))] :
    EnoughInjectives (L.SmoothSheaf (ModuleCat.{w} R) J) :=
  EnoughInjectives.of_adjunction (smoothAdjunction L J)

end AbelianStructure

end LocalActionSystem

end Modules

namespace LocalActionSystem

/-- Over a small site, with the ring and the modules in the universe of the
site, locally discrete module sheaves have enough injectives: module sheaves form
a Grothendieck abelian category in Mathlib. -/
theorem smoothSheaf_enoughInjectives_of_small {T : Type w} [SmallCategory T]
    (L : LocalActionSystem T G) (J : GrothendieckTopology T) (R : Type w) [CommRing R]
    [L.HasAdmissibleRefinements J] :
    EnoughInjectives (L.SmoothSheaf (ModuleCat.{w} R) J) :=
  inferInstance

end LocalActionSystem

end Langlands.Sheaf.Equivariant
