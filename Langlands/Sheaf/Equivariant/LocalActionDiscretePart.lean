import Langlands.Sheaf.Equivariant.LocalAction
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Abelian.Subcategory
import Mathlib.CategoryTheory.Adjunction.Reflective
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# The discrete part of a sheaf for a local action system

For a local action system on a site, a sheaf is discrete (Berkovich's
Definition 1.4.1 shape) when every admissible local action acts on its
sections with open stabilizers. Assume that every covering sieve of an object
with an admissible local action contains a finite family of arrows from objects
with admissible local actions, each compatible with the actions on small open
subgroups, generating a covering sieve. Then the sections of a module sheaf
whose restrictions along all arrows from admissible objects are discrete form a
subsheaf, the discrete part. It is right adjoint to the inclusion of discrete
sheaves; discrete module sheaves form an abelian category with exact inclusion
and with enough injectives when all module sheaves have enough injectives.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject

universe v u uG uR w

variable {T : Type u} [Category.{v} T] {G : Type uG} [Group G] [TopologicalSpace G]

section Equivariance

/-- An arrow `f : V ⟶ U` is locally equivariant from a local action `b` of `H'`
on `V` to a local action `a` of `H` on `U` when, for every open subgroup `K` of
`H'`, a smaller open subgroup `M` of `H` acts compatibly through elements of
`K`: for `h ∈ M` there is `k ∈ K` with `b k` followed by `f` equal to `f`
followed by `a h`. -/
def IsLocallyEquivariant {U V : T} {H H' : OpenSubgroup G}
    (a : (H : Subgroup G) →* (End U)ᵐᵒᵖ) (b : (H' : Subgroup G) →* (End V)ᵐᵒᵖ)
    (f : V ⟶ U) : Prop :=
  ∀ K : OpenSubgroup G, K ≤ H' → ∃ M : OpenSubgroup G, M ≤ H ∧
    ∀ h : (H : Subgroup G), (h : G) ∈ M → ∃ k : (H' : Subgroup G), (k : G) ∈ K ∧
      (b k).unop ≫ f = f ≫ (a h).unop

/-- An arrow intertwining two local actions on a common open subgroup is locally
equivariant. -/
theorem isLocallyEquivariant_of_intertwines {U V : T} {H H' : OpenSubgroup G}
    {a : (H : Subgroup G) →* (End U)ᵐᵒᵖ} {b : (H' : Subgroup G) →* (End V)ᵐᵒᵖ}
    {f : V ⟶ U} (N : OpenSubgroup G) (hNH : N ≤ H) (hNH' : N ≤ H')
    (hf : ∀ (g : G) (hg : g ∈ N), (b ⟨g, hNH' hg⟩).unop ≫ f = f ≫ (a ⟨g, hNH hg⟩).unop) :
    IsLocallyEquivariant a b f := by
  intro K _
  refine ⟨N ⊓ K, inf_le_left.trans hNH, fun h hh => ?_⟩
  obtain ⟨hhN, hhK⟩ := OpenSubgroup.mem_inf.1 hh
  exact ⟨⟨h, hNH' hhN⟩, hhK, hf h hhN⟩

variable {A : Type*} [Category A] {FA : A → A → Type*} {CA : A → Type*}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]

/-- Discreteness descends along a finite family of locally equivariant arrows
which separates sections: if the restriction of `s` along each arrow is
discrete, then `s` is discrete. The fixing subgroup is the finite intersection
of the subgroups provided by local equivariance. -/
theorem IsDiscreteSection.of_finite_family {F : Tᵒᵖ ⥤ A} {U : T} {H : OpenSubgroup G}
    {a : (H : Subgroup G) →* (End U)ᵐᵒᵖ} {s : ToType (F.obj (op U))} {n : ℕ}
    {V : Fin n → T} {H' : Fin n → OpenSubgroup G}
    {b : ∀ i, (H' i : Subgroup G) →* (End (V i))ᵐᵒᵖ} {f : ∀ i, V i ⟶ U}
    (hf : ∀ i, IsLocallyEquivariant a (b i) (f i))
    (hs : ∀ i, IsDiscreteSection F (b i) (F.map (f i).op s))
    (hsep : ∀ t t' : ToType (F.obj (op U)),
      (∀ i, F.map (f i).op t = F.map (f i).op t') → t = t') :
    IsDiscreteSection F a s := by
  choose K hKH hK using hs
  choose M hMH hM using fun i => hf i (K i) (hKH i)
  refine ⟨H ⊓ Finset.univ.inf M, inf_le_left, fun h hh => ?_⟩
  have hhM : ∀ i, (h : G) ∈ M i := fun i =>
    (Finset.inf_le (f := M) (Finset.mem_univ i)) (inf_le_right (a := H) hh)
  apply hsep
  intro i
  obtain ⟨k, hkK, hk⟩ := hM i h (hhM i)
  have h₁ : F.map (f i).op (F.map (a h).unop.op s) = F.map (f i ≫ (a h).unop).op s := by
    rw [op_comp, F.map_comp, CategoryTheory.comp_apply]
  have h₂ : F.map ((b i k).unop ≫ f i).op s =
      F.map (b i k).unop.op (F.map (f i).op s) := by
    rw [op_comp, F.map_comp, CategoryTheory.comp_apply]
  rw [h₁, ← hk, h₂, hK i k hkK]

end Equivariance

namespace LocalActionSystem

variable (L : LocalActionSystem T G) (J : GrothendieckTopology T)

/-- Every covering sieve of an object with an admissible local action contains
a finite family of arrows from objects with admissible local actions, each
locally equivariant, which generates a covering sieve. This abstracts the
compactness of the objects and the canonical local actions of Berkovich's Key
Lemma. -/
class HasFiniteEquivariantRefinements : Prop where
  exists_refinement : ∀ ⦃U : T⦄ ⦃H : OpenSubgroup G⦄ ⦃a : (H : Subgroup G) →* (End U)ᵐᵒᵖ⦄,
    L.IsAdmissible U H a → ∀ ⦃S : Sieve U⦄, S ∈ J U →
      ∃ (n : ℕ) (V : Fin n → T) (H' : Fin n → OpenSubgroup G)
        (b : ∀ i, (H' i : Subgroup G) →* (End (V i))ᵐᵒᵖ) (f : ∀ i, V i ⟶ U),
        (∀ i, L.IsAdmissible (V i) (H' i) (b i)) ∧ (∀ i, S (f i)) ∧
        (∀ i, IsLocallyEquivariant a (b i) (f i)) ∧ Sieve.ofArrows V f ∈ J U

end LocalActionSystem

namespace LocalActionSystem

variable (L : LocalActionSystem T G) (A : Type*) [Category A] {FA : A → A → Type*}
variable {CA : A → Type*} [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
variable (J : GrothendieckTopology T)

/-- The full subcategory of discrete sheaves (Berkovich's Definition 1.4.1 shape). -/
abbrev DiscreteSheaf := (L.discreteSheafProperty A J).FullSubcategory

/-- The inclusion of discrete sheaves into all sheaves. -/
abbrev discreteSheafInclusion : L.DiscreteSheaf A J ⥤ Sheaf J A :=
  (L.discreteSheafProperty A J).ι

end LocalActionSystem

section Modules

variable {R : Type uR} [CommRing R]

theorem isDiscreteSection_zero (F : Tᵒᵖ ⥤ ModuleCat.{w} R) {U : T} {H : OpenSubgroup G}
    (a : (H : Subgroup G) →* (End U)ᵐᵒᵖ) : IsDiscreteSection F a (0 : F.obj (op U)) :=
  ⟨H, le_rfl, fun _ _ => map_zero _⟩

theorem IsDiscreteSection.add {F : Tᵒᵖ ⥤ ModuleCat.{w} R} {U : T} {H : OpenSubgroup G}
    {a : (H : Subgroup G) →* (End U)ᵐᵒᵖ} {s t : F.obj (op U)}
    (hs : IsDiscreteSection F a s) (ht : IsDiscreteSection F a t) :
    IsDiscreteSection F a (s + t) := by
  obtain ⟨K, hKH, hK⟩ := hs
  obtain ⟨K', -, hK'⟩ := ht
  refine ⟨K ⊓ K', inf_le_left.trans hKH, fun h hh => ?_⟩
  rw [map_add, hK h (inf_le_left (a := K) hh), hK' h (inf_le_right (a := K) hh)]

theorem IsDiscreteSection.smul {F : Tᵒᵖ ⥤ ModuleCat.{w} R} {U : T} {H : OpenSubgroup G}
    {a : (H : Subgroup G) →* (End U)ᵐᵒᵖ} {s : F.obj (op U)}
    (hs : IsDiscreteSection F a s) (r : R) : IsDiscreteSection F a (r • s) := by
  obtain ⟨K, hKH, hK⟩ := hs
  exact ⟨K, hKH, fun h hh => by rw [map_smul, hK h hh]⟩

/-- A module-valued sheaf is separated: sections with equal restrictions along a
covering sieve are equal. The submodule spanned by their difference maps to
zero after every restriction in the sieve, so the sheaf condition at that
submodule identifies its inclusion with zero. -/
theorem isSeparated_of_isSheaf {J : GrothendieckTopology T} {F : Tᵒᵖ ⥤ ModuleCat.{w} R}
    (hF : Presheaf.IsSheaf J F) {U : T} {S : Sieve U} (hS : S ∈ J U)
    {x y : F.obj (op U)} (h : ∀ ⦃W : T⦄ (g : W ⟶ U), S g → F.map g.op x = F.map g.op y) :
    x = y := by
  let E : Submodule R (F.obj (op U)) := Submodule.span R {x - y}
  have hE : ModuleCat.ofHom E.subtype = (0 : ModuleCat.of R E ⟶ F.obj (op U)) := by
    apply hF.hom_ext ⟨S, hS⟩
    rintro ⟨W, g, hg⟩
    ext ⟨e, he⟩
    change (F.map g.op).hom e = (F.map g.op).hom 0
    rw [map_zero]
    refine Submodule.span_induction (p := fun e _ => (F.map g.op).hom e = 0) ?_ ?_ ?_ ?_ he
    · rintro _ rfl
      rw [map_sub]
      exact sub_eq_zero.2 (h g hg)
    · exact map_zero _
    · intro _ _ _ _ h₁ h₂
      rw [map_add, h₁, h₂, add_zero]
    · intro r _ _ h₁
      rw [map_smul, h₁, smul_zero]
  have := congrArg (fun φ => φ.hom (⟨x - y, Submodule.subset_span rfl⟩ : E)) hE
  exact sub_eq_zero.1 this

variable (L : LocalActionSystem T G)

/-- The sections whose restrictions along all arrows from objects with an
admissible local action are discrete for that action. -/
def discreteSubmodule (F : Tᵒᵖ ⥤ ModuleCat.{w} R) (U : T) : Submodule R (F.obj (op U)) where
  carrier := {s | ∀ (V : T) (H : OpenSubgroup G) (b : (H : Subgroup G) →* (End V)ᵐᵒᵖ),
    L.IsAdmissible V H b → ∀ f : V ⟶ U, IsDiscreteSection F b (F.map f.op s)}
  add_mem' hs ht V H b hb f := by
    rw [map_add]
    exact (hs V H b hb f).add (ht V H b hb f)
  zero_mem' V H b _ f := by
    rw [map_zero]
    exact isDiscreteSection_zero F b
  smul_mem' r s hs V H b hb f := by
    rw [map_smul]
    exact (hs V H b hb f).smul r

theorem mem_discreteSubmodule_iff {F : Tᵒᵖ ⥤ ModuleCat.{w} R} {U : T} (s : F.obj (op U)) :
    s ∈ discreteSubmodule L F U ↔ ∀ (V : T) (H : OpenSubgroup G)
      (b : (H : Subgroup G) →* (End V)ᵐᵒᵖ), L.IsAdmissible V H b →
        ∀ f : V ⟶ U, IsDiscreteSection F b (F.map f.op s) :=
  Iff.rfl

/-- Restriction preserves the discrete submodules. -/
theorem map_mem_discreteSubmodule (F : Tᵒᵖ ⥤ ModuleCat.{w} R) {U U' : T} (g : U' ⟶ U)
    {s : F.obj (op U)} (hs : s ∈ discreteSubmodule L F U) :
    F.map g.op s ∈ discreteSubmodule L F U' := by
  intro V H b hb f
  have : F.map f.op (F.map g.op s) = F.map (f ≫ g).op s := by
    rw [op_comp, F.map_comp, CategoryTheory.comp_apply]
  rw [this]
  exact hs V H b hb (f ≫ g)

/-- Morphisms of presheaves preserve the discrete submodules. -/
theorem map_mem_discreteSubmodule_of_hom {F F' : Tᵒᵖ ⥤ ModuleCat.{w} R} (φ : F ⟶ F')
    {U : T} {s : F.obj (op U)} (hs : s ∈ discreteSubmodule L F U) :
    φ.app (op U) s ∈ discreteSubmodule L F' U := by
  intro V H b hb f
  rw [← NatTrans.naturality_apply]
  exact (hs V H b hb f).map φ

/-- On an object with an admissible local action, every section of the discrete
submodule is discrete. -/
theorem isDiscreteSection_of_mem_discreteSubmodule {F : Tᵒᵖ ⥤ ModuleCat.{w} R} {U : T}
    {H : OpenSubgroup G} {a : (H : Subgroup G) →* (End U)ᵐᵒᵖ} (ha : L.IsAdmissible U H a)
    {s : F.obj (op U)} (hs : s ∈ discreteSubmodule L F U) : IsDiscreteSection F a s := by
  have := hs U H a ha (𝟙 U)
  rwa [op_id, F.map_id, CategoryTheory.id_apply] at this

/-- A presheaf is discrete exactly when all its sections lie in the discrete
submodules. -/
theorem isDiscrete_iff_forall_mem (F : Tᵒᵖ ⥤ ModuleCat.{w} R) :
    L.IsDiscrete F ↔ ∀ (U : T) (s : F.obj (op U)), s ∈ discreteSubmodule L F U := by
  constructor
  · intro hF U s V H b hb f
    exact hF V H b hb _
  · intro hF U H a ha s
    exact isDiscreteSection_of_mem_discreteSubmodule L ha (hF U s)

variable {L} {J : GrothendieckTopology T}

/-- Membership in the discrete submodules is local. Restrict an arrow from an
admissible object to the pulled-back covering sieve, refine it by a finite
locally equivariant family, and apply descent of discreteness. -/
theorem mem_discreteSubmodule_of_covering [L.HasFiniteEquivariantRefinements J]
    {F : Tᵒᵖ ⥤ ModuleCat.{w} R} (hF : Presheaf.IsSheaf J F) {U : T} (s : F.obj (op U))
    {S : Sieve U} (hS : S ∈ J U)
    (h : ∀ ⦃W : T⦄ (g : W ⟶ U), S g → F.map g.op s ∈ discreteSubmodule L F W) :
    s ∈ discreteSubmodule L F U := by
  intro V H b hb f
  obtain ⟨n, W, H', c, g, hc, hgS, hg, hcov⟩ :=
    LocalActionSystem.HasFiniteEquivariantRefinements.exists_refinement hb (J.pullback_stable f hS)
  refine IsDiscreteSection.of_finite_family hg (fun i => ?_) (fun t t' htt' => ?_)
  · have hmem := h (g i ≫ f) (hgS i)
    have hW := isDiscreteSection_of_mem_discreteSubmodule L (hc i) hmem
    have : F.map (g i).op (F.map f.op s) = F.map (g i ≫ f).op s := by
      rw [op_comp, F.map_comp, CategoryTheory.comp_apply]
    rw [this]
    exact hW
  · refine isSeparated_of_isSheaf hF hcov ?_
    rintro Z _ ⟨Y, k, _, ⟨i⟩, rfl⟩
    rw [op_comp, F.map_comp, CategoryTheory.comp_apply, CategoryTheory.comp_apply, htt' i]

variable (L)

/-- The presheaf of discrete parts. -/
def discretePresheaf (F : Tᵒᵖ ⥤ ModuleCat.{w} R) : Tᵒᵖ ⥤ ModuleCat.{w} R where
  obj U := ModuleCat.of R (discreteSubmodule L F U.unop)
  map {U V} f := ModuleCat.ofHom ((F.map f).hom.restrict fun _ hs =>
    map_mem_discreteSubmodule L F f.unop hs)
  map_id U := by
    ext s
    simp
  map_comp f g := by
    ext s
    simp

/-- The inclusion of the discrete part. -/
def discretePresheafι (F : Tᵒᵖ ⥤ ModuleCat.{w} R) : discretePresheaf L F ⟶ F where
  app U := ModuleCat.ofHom (discreteSubmodule L F U.unop).subtype
  naturality _ _ _ := rfl

theorem discretePresheafι_app_injective (F : Tᵒᵖ ⥤ ModuleCat.{w} R) (U : Tᵒᵖ) :
    Function.Injective ((discretePresheafι L F).app U) :=
  Subtype.val_injective

/-- Morphisms of presheaves restrict to the discrete parts. -/
def discretePresheafMap {F F' : Tᵒᵖ ⥤ ModuleCat.{w} R} (φ : F ⟶ F') :
    discretePresheaf L F ⟶ discretePresheaf L F' where
  app U := ModuleCat.ofHom ((φ.app U).hom.restrict fun _ hs =>
    map_mem_discreteSubmodule_of_hom L φ hs)
  naturality U V f := by
    ext s
    apply Subtype.ext
    exact congrArg (fun k => k.hom s.1) (φ.naturality f)

/-- The discrete part, functorially in the presheaf. -/
@[simps]
def discretePresheafFunctor : (Tᵒᵖ ⥤ ModuleCat.{w} R) ⥤ (Tᵒᵖ ⥤ ModuleCat.{w} R) where
  obj := discretePresheaf L
  map := discretePresheafMap L
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The discrete part of a presheaf is discrete. -/
theorem isDiscrete_discretePresheaf (F : Tᵒᵖ ⥤ ModuleCat.{w} R) :
    L.IsDiscrete (discretePresheaf L F) := by
  intro U H a ha s
  have hs := isDiscreteSection_of_mem_discreteSubmodule L ha s.2
  exact IsDiscreteSection.of_injective (discretePresheafι L F)
    (discretePresheafι_app_injective L F _) hs

variable {L}

/-- The discrete part of a sheaf is a sheaf. A compatible family of maps into
the discrete parts glues in the ambient sheaf; every value of the gluing has
restrictions in the discrete parts along a covering sieve, so it lies in the
discrete part by locality. -/
theorem discretePresheaf_isSheaf [L.HasFiniteEquivariantRefinements J]
    {F : Tᵒᵖ ⥤ ModuleCat.{w} R} (hF : Presheaf.IsSheaf J F) :
    Presheaf.IsSheaf J (discretePresheaf L F) := by
  intro E U S hS
  refine Presieve.IsSeparatedFor.isSheafFor (fun x t₁ t₂ h₁ h₂ => ?_) (fun x hx => ?_)
  · -- separatedness: compose with the injective inclusion
    have key : t₁ ≫ (discretePresheafι L F).app (op U) =
        t₂ ≫ (discretePresheafι L F).app (op U) := by
      apply hF.hom_ext ⟨S, hS⟩
      rintro ⟨W, g, hg⟩
      simp only [Category.assoc]
      rw [← (discretePresheafι L F).naturality]
      rw [← Category.assoc, ← Category.assoc]
      change (t₁ ≫ (discretePresheaf L F).map g.op) ≫ _ =
        (t₂ ≫ (discretePresheaf L F).map g.op) ≫ _
      rw [show t₁ ≫ (discretePresheaf L F).map g.op = x g hg from h₁ g hg,
        show t₂ ≫ (discretePresheaf L F).map g.op = x g hg from h₂ g hg]
    change (t₁ : E ⟶ (discretePresheaf L F).obj (op U)) = t₂
    refine ModuleCat.hom_ext (LinearMap.ext fun e => ?_)
    apply discretePresheafι_app_injective L F (op U)
    exact congrArg (fun φ => φ.hom e) key
  · -- existence: glue in the ambient sheaf and restrict the codomain
    let y : Presieve.FamilyOfElements (F ⋙ coyoneda.obj (op E)) S.arrows :=
      fun W g hg => x g hg ≫ (discretePresheafι L F).app (op W)
    have hy : y.Compatible := by
      intro W₁ W₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w
      change (x f₁ h₁ ≫ _) ≫ F.map g₁.op = (x f₂ h₂ ≫ _) ≫ F.map g₂.op
      rw [Category.assoc, Category.assoc, ← (discretePresheafι L F).naturality,
        ← (discretePresheafι L F).naturality, ← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ (discretePresheafι L F).app (op Z)) (hx g₁ g₂ h₁ h₂ w)
    let t := (hF E S hS).amalgamate y hy
    have ht : ∀ ⦃W : T⦄ (g : W ⟶ U) (hg : S g),
        t ≫ F.map g.op = x g hg ≫ (discretePresheafι L F).app (op W) :=
      fun W g hg => (hF E S hS).valid_glue hy g hg
    have hmem : ∀ e : E, t.hom e ∈ discreteSubmodule L F U := fun e =>
      mem_discreteSubmodule_of_covering (J := J) hF _ hS fun W g hg => by
        have := congrArg (fun φ => φ.hom e) (ht g hg)
        change (F.map g.op).hom (t.hom e) = ((x g hg).hom e).1 at this
        change (F.map g.op).hom (t.hom e) ∈ _
        rw [this]
        exact ((x g hg).hom e).2
    refine ⟨ModuleCat.ofHom (LinearMap.codRestrict _ t.hom hmem), fun W g hg => ?_⟩
    change ModuleCat.ofHom (LinearMap.codRestrict _ t.hom hmem) ≫
      (discretePresheaf L F).map g.op = x g hg
    refine ModuleCat.hom_ext (LinearMap.ext fun e => ?_)
    apply discretePresheafι_app_injective L F (op W)
    exact congrArg (fun φ => φ.hom e) (ht g hg)

variable (L J)
variable [L.HasFiniteEquivariantRefinements J]

/-- The discrete subsheaf of a module sheaf. -/
def discreteSubsheafFunctor : Sheaf J (ModuleCat.{w} R) ⥤ Sheaf J (ModuleCat.{w} R) :=
  ObjectProperty.lift (Presheaf.IsSheaf J (A := ModuleCat.{w} R))
    (sheafToPresheaf J _ ⋙ discretePresheafFunctor L)
    fun F => discretePresheaf_isSheaf F.property

/-- The inclusion of the discrete subsheaf. -/
def discreteSubsheafι : discreteSubsheafFunctor L J ⟶ 𝟭 (Sheaf J (ModuleCat.{w} R)) where
  app F := ObjectProperty.homMk (discretePresheafι L F.obj)
  naturality _ _ _ := rfl


theorem isDiscrete_discreteSubsheaf (F : Sheaf J (ModuleCat.{w} R)) :
    L.discreteSheafProperty (ModuleCat.{w} R) J ((discreteSubsheafFunctor L J).obj F) :=
  isDiscrete_discretePresheaf L F.obj

/-- The discrete part of a module sheaf, as a discrete sheaf. -/
def discreteCoreflector : Sheaf J (ModuleCat.{w} R) ⥤ L.DiscreteSheaf (ModuleCat.{w} R) J :=
  (L.discreteSheafProperty (ModuleCat.{w} R) J).lift (discreteSubsheafFunctor L J)
    (isDiscrete_discreteSubsheaf L J)

variable {L J}

/-- A morphism from a discrete sheaf factors through the discrete subsheaf. -/
def discreteLift {S F : Sheaf J (ModuleCat.{w} R)}
    (hS : L.discreteSheafProperty (ModuleCat.{w} R) J S) (f : S ⟶ F) :
    S ⟶ (discreteSubsheafFunctor L J).obj F :=
  ObjectProperty.homMk
    { app U := ModuleCat.ofHom (LinearMap.codRestrict _ (f.hom.app U).hom fun s =>
        map_mem_discreteSubmodule_of_hom L f.hom ((isDiscrete_iff_forall_mem L S.obj).1 hS _ s))
      naturality U V g := by
        ext s
        apply Subtype.ext
        exact congrArg (fun k => k.hom s) (f.hom.naturality g) }

@[reassoc (attr := simp)]
theorem discreteLift_comp_ι {S F : Sheaf J (ModuleCat.{w} R)}
    (hS : L.discreteSheafProperty (ModuleCat.{w} R) J S) (f : S ⟶ F) :
    discreteLift hS f ≫ (discreteSubsheafι L J).app F = f :=
  rfl

variable (L J)

/-- The discrete part is right adjoint to the inclusion of discrete sheaves. -/
def discreteAdjunction : L.discreteSheafInclusion (ModuleCat.{w} R) J ⊣ discreteCoreflector L J :=
  Adjunction.mkOfHomEquiv
    { homEquiv S F :=
        { toFun f := ObjectProperty.homMk (discreteLift S.property f)
          invFun g := g.hom ≫ (discreteSubsheafι L J).app F
          left_inv _ := rfl
          right_inv _ := rfl }
      homEquiv_naturality_left_symm _ _ := rfl
      homEquiv_naturality_right _ _ := rfl }

section AbelianStructure

variable [HasSheafify J (ModuleCat.{w} R)]

variable {J} in
/-- Monomorphisms of module sheaves are injective on sections. -/
theorem injective_app_of_mono {F F' : Sheaf J (ModuleCat.{w} R)} (f : F ⟶ F') [Mono f]
    (U : Tᵒᵖ) : Function.Injective (f.hom.app U) := by
  have : Mono ((sheafToPresheaf J (ModuleCat.{w} R)).map f) := inferInstance
  have : Mono (f.hom.app U) := inferInstance
  exact (ModuleCat.mono_iff_injective _).1 this

instance mono_discreteSubsheafι_app (F : Sheaf J (ModuleCat.{w} R)) :
    Mono ((discreteSubsheafι L J).app F) := by
  have : ∀ U, Mono ((discretePresheafι L F.obj).app U) := fun U =>
    (ModuleCat.mono_iff_injective _).2 (discretePresheafι_app_injective L F.obj U)
  have : Mono ((sheafToPresheaf J (ModuleCat.{w} R)).map ((discreteSubsheafι L J).app F)) :=
    NatTrans.mono_of_mono_app (discretePresheafι L F.obj)
  exact (sheafToPresheaf J (ModuleCat.{w} R)).mono_of_mono_map this

/-- A subsheaf of a discrete module sheaf is discrete. -/
instance discreteSheafProperty_isClosedUnderSubobjects :
    (L.discreteSheafProperty (ModuleCat.{w} R) J).IsClosedUnderSubobjects where
  prop_of_mono f _ hY :=
    LocalActionSystem.IsDiscrete.of_injective L f.hom (injective_app_of_mono f) hY

/-- A module sheaf whose discrete part is all of it is discrete. -/
theorem discreteSheafProperty_of_isIso {F : Sheaf J (ModuleCat.{w} R)}
    [IsIso ((discreteSubsheafι L J).app F)] : L.discreteSheafProperty (ModuleCat.{w} R) J F :=
  (L.discreteSheafProperty (ModuleCat.{w} R) J).prop_of_mono
    (inv ((discreteSubsheafι L J).app F)) (isDiscrete_discreteSubsheaf L J F)

/-- A quotient of a discrete module sheaf is discrete: an epimorphism from a
discrete sheaf factors through the discrete subsheaf of its target, whose
inclusion is then a monomorphism and an epimorphism, hence an isomorphism. -/
instance discreteSheafProperty_isClosedUnderQuotients :
    (L.discreteSheafProperty (ModuleCat.{w} R) J).IsClosedUnderQuotients where
  prop_of_epi {X Y} f _ hX := by
    have hfac := discreteLift_comp_ι (L := L) (J := J) hX f
    have : Epi ((discreteSubsheafι L J).app Y) := epi_of_epi_fac hfac
    have : IsIso ((discreteSubsheafι L J).app Y) := isIso_of_mono_of_epi _
    exact discreteSheafProperty_of_isIso L J

/-- The zero module sheaf is discrete. -/
instance discreteSheafProperty_containsZero :
    (L.discreteSheafProperty (ModuleCat.{w} R) J).ContainsZero where
  exists_zero := by
    refine ⟨0, isZero_zero _, ?_⟩
    let f : (0 : Sheaf J (ModuleCat.{w} R)) ⟶ (discreteSubsheafFunctor L J).obj 0 := 0
    have : Mono f := ⟨fun g h _ => (isZero_zero _).eq_of_tgt g h⟩
    exact (L.discreteSheafProperty (ModuleCat.{w} R) J).prop_of_mono f
      (isDiscrete_discreteSubsheaf L J 0)

omit [HasSheafify J (ModuleCat.{w} R)] in
variable {J} in
/-- Sections of a finite limit of module sheaves are determined by their
projections. -/
theorem sheaf_limit_sections_ext {K : Type} [SmallCategory K] [FinCategory K]
    (D : K ⥤ Sheaf J (ModuleCat.{w} R)) {U : T} (x y : (limit D).obj.obj (op U))
    (h : ∀ k, (limit.π D k).hom.app (op U) x = (limit.π D k).hom.app (op U) y) : x = y :=
  Concrete.isLimit_ext (D ⋙ sheafToPresheaf J _ ⋙ (evaluation _ _).obj (op U))
    (isLimitOfPreserves (sheafToPresheaf J _ ⋙ (evaluation _ _).obj (op U)) (limit.isLimit D))
    x y h

/-- A binary product of discrete module sheaves is discrete: a common open
subgroup fixes the two projections of a section. -/
instance discreteSheafProperty_isClosedUnderBinaryProducts :
    (L.discreteSheafProperty (ModuleCat.{w} R) J).IsClosedUnderBinaryProducts :=
  ObjectProperty.IsClosedUnderLimitsOfShape.mk' (by
    rintro _ ⟨D, hD⟩ U H a ha s
    obtain ⟨K₁, hK₁, h₁⟩ := hD ⟨.left⟩ U H a ha ((limit.π D ⟨.left⟩).hom.app (op U) s)
    obtain ⟨K₂, -, h₂⟩ := hD ⟨.right⟩ U H a ha ((limit.π D ⟨.right⟩).hom.app (op U) s)
    refine ⟨K₁ ⊓ K₂, inf_le_left.trans hK₁, fun h hh => ?_⟩
    apply sheaf_limit_sections_ext D
    rintro ⟨⟨⟩⟩
    · rw [NatTrans.naturality_apply]
      exact h₁ h (inf_le_left (a := K₁) hh)
    · rw [NatTrans.naturality_apply]
      exact h₂ h (inf_le_right (a := K₁) hh))

/-- Finite products of discrete module sheaves are discrete. -/
instance discreteSheafProperty_isClosedUnderFiniteProducts :
    (L.discreteSheafProperty (ModuleCat.{w} R) J).IsClosedUnderFiniteProducts :=
  ObjectProperty.IsClosedUnderFiniteProducts.mk'

/-- Discrete module sheaves form an abelian category. -/
instance discreteSheaf_abelian : Abelian (L.DiscreteSheaf (ModuleCat.{w} R) J) :=
  inferInstance

/-- The inclusion of discrete sheaves preserves monomorphisms. -/
instance discreteSheafInclusion_preservesMonomorphisms :
    (L.discreteSheafInclusion (ModuleCat.{w} R) J).PreservesMonomorphisms :=
  ObjectProperty.preservesMonomorphisms_ι_of_isNormalEpiCategory _

/-- The inclusion of discrete sheaves preserves epimorphisms. -/
instance discreteSheafInclusion_preservesEpimorphisms :
    (L.discreteSheafInclusion (ModuleCat.{w} R) J).PreservesEpimorphisms :=
  ObjectProperty.preservesEpimorphisms_ι_of_isNormalMonoCategory _

/-- The inclusion of discrete sheaves preserves finite limits: kernels of
discrete sheaves are computed among all sheaves. -/
instance discreteSheafInclusion_preservesFiniteLimits :
    PreservesFiniteLimits (L.discreteSheafInclusion (ModuleCat.{w} R) J) :=
  have := (L.discreteSheafProperty (ModuleCat.{w} R) J).preservesKernels_ι
  Functor.preservesFiniteLimits_of_preservesKernels _

/-- The inclusion of discrete sheaves preserves finite colimits: cokernels of
discrete sheaves are computed among all sheaves. -/
instance discreteSheafInclusion_preservesFiniteColimits :
    PreservesFiniteColimits (L.discreteSheafInclusion (ModuleCat.{w} R) J) :=
  have := (L.discreteSheafProperty (ModuleCat.{w} R) J).preservesCokernels_ι
  Functor.preservesFiniteColimits_of_preservesCokernels _

/-- The discrete part of an injective module sheaf is injective among discrete
sheaves. -/
theorem injective_discreteCoreflector_obj (I : Sheaf J (ModuleCat.{w} R)) [Injective I] :
    Injective ((discreteCoreflector L J).obj I) :=
  (discreteAdjunction L J).map_injective I inferInstance

/-- Discrete module sheaves have enough injectives when module sheaves do. -/
instance discreteSheaf_enoughInjectives [EnoughInjectives (Sheaf J (ModuleCat.{w} R))] :
    EnoughInjectives (L.DiscreteSheaf (ModuleCat.{w} R) J) :=
  EnoughInjectives.of_adjunction (discreteAdjunction L J)

end AbelianStructure

end Modules

/-- Over a small site, with the ring and the modules in the universe of the
site, discrete module sheaves have enough injectives: module sheaves form a
Grothendieck abelian category in Mathlib. -/
theorem discreteSheaf_enoughInjectives_of_small {T : Type w} [SmallCategory T]
    (L : LocalActionSystem T G) (J : GrothendieckTopology T) (R : Type w) [CommRing R]
    [L.HasFiniteEquivariantRefinements J] :
    EnoughInjectives (L.DiscreteSheaf (ModuleCat.{w} R) J) :=
  inferInstance

end Langlands.Sheaf.Equivariant
