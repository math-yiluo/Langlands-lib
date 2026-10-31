import Langlands.Geometry.Analytic.GeneralizedAffinoid.InducedUnit

/-! # Bounded extension into actual affinoid-family actions -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.InducedAction

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {G : Type v} [Group G] [TopologicalSpace G] (H : Subgroup G)

/-- Include a copy by the bounded identity on its original quotient algebra. -/
def copyMap (X : NormContinuousSpace K H) (c : G ⧸ H) :
    localFamily H X ⟶ family H X.unop where
  indexMap _ := c
  pullback _ := BoundedAlgHom.id K X.unop.obj.V

/-- Assemble actual bounded maps on the copies, including empty components. -/
def assembleFamilyMap {X : NormContinuousSpace K H} {Y : AffinoidFamily.{u, v} K}
    (f : G ⧸ H → (localFamily H X ⟶ Y)) : family H X.unop ⟶ Y where
  indexMap c := (f c).indexMap PUnit.unit
  pullback c := (f c).pullback PUnit.unit

@[simp]
theorem copyMap_assembleFamilyMap {X : NormContinuousSpace K H}
    {Y : AffinoidFamily.{u, v} K} (f : G ⧸ H → (localFamily H X ⟶ Y))
    (c : G ⧸ H) :
    copyMap H X c ≫ assembleFamilyMap H f = f c := by
  apply AffinoidFamily.Hom.ext
    (f := copyMap H X c ≫ assembleFamilyMap H f) (g := f c)
    (funext fun i => by cases i; rfl)
  apply heq_of_eq
  funext i
  cases i
  exact BoundedAlgHom.ext fun _ => rfl

/-- Complete family arrows are determined by the bounded maps on every copy. -/
theorem familyHom_ext {X : NormContinuousSpace K H}
    {Y : AffinoidFamily.{u, v} K} {f k : family H X.unop ⟶ Y}
    (h : ∀ c, copyMap H X c ≫ f = copyMap H X c ≫ k) : f = k := by
  cases f with
  | mk fi fp =>
    cases k with
    | mk ki kp =>
      have hi : fi = ki := funext fun c =>
        congrFun (congrArg AffinoidFamily.Hom.indexMap (h c)) PUnit.unit
      subst ki
      apply AffinoidFamily.Hom.ext
        (f := ⟨fi, fp⟩) (g := ⟨fi, kp⟩) rfl
      apply heq_of_eq
      funext c
      have hc := congrArg
        (fun q : localFamily H X ⟶ Y =>
          (⟨q.indexMap PUnit.unit, q.pullback PUnit.unit⟩ :
            Σ j, BoundedAlgHom K (Y.algebra j) X.unop.obj.V)) (h c)
      exact eq_of_heq (Sigma.mk.inj hc).2

/-- The correction equation holds for the complete bounded inclusion maps. -/
theorem copyMap_action (X : NormContinuousSpace K H) (g : G) (c : G ⧸ H) :
    copyMap H X c ≫ actionMap H X.unop g =
      localActionMap H X (correction H g c) ≫ copyMap H X (g • c) := by
  apply AffinoidFamily.Hom.ext
    (f := copyMap H X c ≫ actionMap H X.unop g)
    (g := localActionMap H X (correction H g c) ≫ copyMap H X (g • c)) rfl
  apply heq_of_eq
  funext i
  exact BoundedAlgHom.ext fun _ => rfl

/-- Separate the original unit's forward representative operator from the copy. -/
theorem unitFamilyMap_eq (X : NormContinuousSpace K H) :
    unitFamilyMap H X =
      localActionMap H X (identityRepresentative H)⁻¹ ≫
        copyMap H X (identityCoset H) := by
  apply AffinoidFamily.Hom.ext
    (f := unitFamilyMap H X)
    (g := localActionMap H X (identityRepresentative H)⁻¹ ≫
      copyMap H X (identityCoset H)) rfl
  apply heq_of_eq
  funext i
  change (X.unop.actionAut (identityRepresentative H)).hom =
    ((X.unop.actionAut (identityRepresentative H)⁻¹).inv).comp
      (BoundedAlgHom.id K X.unop.obj.V)
  rw [map_inv]
  exact BoundedAlgHom.ext fun _ => rfl

omit [TopologicalSpace G] in
/-- Compose the actual target action in categorical order. -/
theorem familyAction_comp (Y : Action (AffinoidFamily.{u, v} K) G) (g k : G) :
    Y.ρ k ≫ Y.ρ g = Y.ρ (g * k) :=
  (Y.ρ.map_mul g k).symm

/-- Copywise extension uses the target action at the chosen coset representative. -/
def extendFamilyMap {X : NormContinuousSpace K H}
    {Y : Action (AffinoidFamily.{u, v} K) G}
    (f : (localFunctor H).obj X ⟶
      (Action.res (AffinoidFamily.{u, v} K) H.subtype).obj Y) :
    family H X.unop ⟶ Y.V :=
  assembleFamilyMap H (fun c => f.hom ≫ Y.ρ c.out)

@[simp]
theorem copyMap_extendFamilyMap {X : NormContinuousSpace K H}
    {Y : Action (AffinoidFamily.{u, v} K) G}
    (f : (localFunctor H).obj X ⟶
      (Action.res (AffinoidFamily.{u, v} K) H.subtype).obj Y)
    (c : G ⧸ H) :
    copyMap H X c ≫ extendFamilyMap H f = f.hom ≫ Y.ρ c.out :=
  copyMap_assembleFamilyMap H _ c

/-- The extension is equivariant as a complete bounded family morphism. -/
theorem extendFamilyMap_equivariant {X : NormContinuousSpace K H}
    {Y : Action (AffinoidFamily.{u, v} K) G}
    (f : (localFunctor H).obj X ⟶
      (Action.res (AffinoidFamily.{u, v} K) H.subtype).obj Y)
    (g : G) :
    actionMap H X.unop g ≫ extendFamilyMap H f =
      extendFamilyMap H f ≫ Y.ρ g := by
  apply familyHom_ext H
  intro c
  let f₀ : localFamily H X ⟶ Y.V := f.hom
  have hc (d : G ⧸ H) : copyMap H X d ≫ extendFamilyMap H f =
      f₀ ≫ Y.ρ d.out := copyMap_extendFamilyMap H f d
  have hf : localActionMap H X (correction H g c) ≫ f₀ =
      f₀ ≫ Y.ρ (correction H g c : G) := f.comm (correction H g c)
  calc
    copyMap H X c ≫ (actionMap H X.unop g ≫ extendFamilyMap H f) =
        localActionMap H X (correction H g c) ≫
          (copyMap H X (g • c) ≫ extendFamilyMap H f) := by
            rw [← Category.assoc, copyMap_action, Category.assoc]
    _ = localActionMap H X (correction H g c) ≫
        (f₀ ≫ Y.ρ (g • c).out) := by rw [hc]
    _ = (f₀ ≫ Y.ρ (correction H g c : G)) ≫ Y.ρ (g • c).out := by
      rw [← Category.assoc, hf]
    _ = f₀ ≫ Y.ρ (g * c.out) := by
      rw [Category.assoc, familyAction_comp, ← correction_spec]
    _ = copyMap H X c ≫ (extendFamilyMap H f ≫ Y.ρ g) := by
      rw [← Category.assoc, hc, Category.assoc, familyAction_comp]

/-- The constructed full-group equivariant bounded extension. -/
def extendFamily {X : NormContinuousSpace K H}
    {Y : Action (AffinoidFamily.{u, v} K) G}
    (f : (localFunctor H).obj X ⟶
      (Action.res (AffinoidFamily.{u, v} K) H.subtype).obj Y) :
    (functor H).obj X ⟶ Y :=
  ⟨extendFamilyMap H f, extendFamilyMap_equivariant H f⟩

omit [TopologicalSpace G] in
@[simp]
theorem out_smul_identityCoset (c : G ⧸ H) :
    c.out • identityCoset H = c := by
  change (QuotientGroup.mk (c.out * 1) : G ⧸ H) = c
  rw [mul_one]
  exact QuotientGroup.out_eq' c

omit [TopologicalSpace G] in
@[simp]
theorem correction_out_identityCoset (c : G ⧸ H) :
    correction H c.out (identityCoset H) = identityRepresentative H := by
  apply Subtype.ext
  rw [correction_coe, out_smul_identityCoset]
  simp [identityRepresentative]

/-- Translating the normalized unit by a chosen representative gives that copy. -/
theorem unitFamilyMap_action (X : NormContinuousSpace K H) (c : G ⧸ H) :
    unitFamilyMap H X ≫ actionMap H X.unop c.out = copyMap H X c := by
  rw [unitFamilyMap_eq, Category.assoc, copyMap_action,
    out_smul_identityCoset, correction_out_identityCoset,
    ← Category.assoc, ← localActionMap_mul, mul_inv_cancel,
    localActionMap_one, Category.id_comp]

/-- The extension agrees with the given bounded arrow on the normalized unit. -/
theorem unitFamilyMap_extendFamilyMap {X : NormContinuousSpace K H}
    {Y : Action (AffinoidFamily.{u, v} K) G}
    (f : (localFunctor H).obj X ⟶
      (Action.res (AffinoidFamily.{u, v} K) H.subtype).obj Y) :
    unitFamilyMap H X ≫ extendFamilyMap H f = f.hom := by
  let f₀ : localFamily H X ⟶ Y.V := f.hom
  have hf : localActionMap H X (identityRepresentative H)⁻¹ ≫ f₀ =
      f₀ ≫ Y.ρ ((identityRepresentative H)⁻¹ : H) :=
    f.comm (identityRepresentative H)⁻¹
  have hc : copyMap H X (identityCoset H) ≫ extendFamilyMap H f =
      f₀ ≫ Y.ρ (identityRepresentative H : G) :=
    copyMap_extendFamilyMap H f (identityCoset H)
  change unitFamilyMap H X ≫ extendFamilyMap H f = f₀
  rw [unitFamilyMap_eq, Category.assoc, hc, ← Category.assoc, hf,
    Category.assoc, familyAction_comp]
  simp

/-- Restrict a full-group bounded map by the constructed subgroup-equivariant unit. -/
def restrictFamily {X : NormContinuousSpace K H}
    {Y : Action (AffinoidFamily.{u, v} K) G}
    (p : (functor H).obj X ⟶ Y) :
    (localFunctor H).obj X ⟶
      (Action.res (AffinoidFamily.{u, v} K) H.subtype).obj Y :=
  (familyUnit H).app X ≫ (Action.res (AffinoidFamily.{u, v} K) H.subtype).map p

@[simp]
theorem restrictFamily_extendFamily {X : NormContinuousSpace K H}
    {Y : Action (AffinoidFamily.{u, v} K) G}
    (f : (localFunctor H).obj X ⟶
      (Action.res (AffinoidFamily.{u, v} K) H.subtype).obj Y) :
    restrictFamily H (extendFamily H f) = f :=
  Action.Hom.ext (unitFamilyMap_extendFamilyMap H f)

@[simp]
theorem extendFamily_restrictFamily {X : NormContinuousSpace K H}
    {Y : Action (AffinoidFamily.{u, v} K) G}
    (p : (functor H).obj X ⟶ Y) :
    extendFamily H (restrictFamily H p) = p := by
  apply Action.Hom.ext
  let p₀ : family H X.unop ⟶ Y.V := p.hom
  change extendFamilyMap H (restrictFamily H p) = p₀
  apply familyHom_ext H
  intro c
  rw [copyMap_extendFamilyMap]
  change (unitFamilyMap H X ≫ p₀) ≫ Y.ρ c.out = copyMap H X c ≫ p₀
  have hp : actionMap H X.unop c.out ≫ p₀ = p₀ ≫ Y.ρ c.out :=
    p.comm c.out
  rw [Category.assoc, ← hp, ← Category.assoc, unitFamilyMap_action]

/-- Actual bounded equivariant maps correspond by restriction and copywise extension. -/
def familyExtensionEquiv {X : NormContinuousSpace K H}
    {Y : Action (AffinoidFamily.{u, v} K) G} :
    ((functor H).obj X ⟶ Y) ≃
      ((localFunctor H).obj X ⟶
        (Action.res (AffinoidFamily.{u, v} K) H.subtype).obj Y) where
  toFun := restrictFamily H
  invFun := extendFamily H
  left_inv := extendFamily_restrictFamily H
  right_inv := restrictFamily_extendFamily H

/-- Uniqueness compares entire family arrows and their original bounded pullbacks. -/
theorem extendFamily_unique {X : NormContinuousSpace K H}
    {Y : Action (AffinoidFamily.{u, v} K) G}
    (f : (localFunctor H).obj X ⟶
      (Action.res (AffinoidFamily.{u, v} K) H.subtype).obj Y)
    (p : (functor H).obj X ⟶ Y)
    (hp : unitFamilyMap H X ≫ p.hom = f.hom) :
    p = extendFamily H f := by
  apply (familyExtensionEquiv H).injective
  change restrictFamily H p = restrictFamily H (extendFamily H f)
  rw [restrictFamily_extendFamily]
  exact Action.Hom.ext hp

/-- Naturality in every original subgroup-equivariant bounded input arrow. -/
theorem familyExtensionEquiv_naturality_left {X X' : NormContinuousSpace K H}
    {Y : Action (AffinoidFamily.{u, v} K) G}
    (f : X' ⟶ X) (p : (functor H).obj X ⟶ Y) :
    familyExtensionEquiv H ((functor H).map f ≫ p) =
      (localFunctor H).map f ≫ familyExtensionEquiv H p := by
  apply Action.Hom.ext
  let p₀ : family H X.unop ⟶ Y.V := p.hom
  change unitFamilyMap H X' ≫ (familyMap H f ≫ p₀) =
    localFamilyMap H f ≫ (unitFamilyMap H X ≫ p₀)
  rw [← Category.assoc, ← unitFamilyMap_naturality, Category.assoc]

/-- Naturality in every bounded equivariant arrow of target family actions. -/
theorem familyExtensionEquiv_naturality_right {X : NormContinuousSpace K H}
    {Y Z : Action (AffinoidFamily.{u, v} K) G}
    (p : (functor H).obj X ⟶ Y) (q : Y ⟶ Z) :
    familyExtensionEquiv H (p ≫ q) =
      familyExtensionEquiv H p ≫
        (Action.res (AffinoidFamily.{u, v} K) H.subtype).map q := by
  apply Action.Hom.ext
  exact (Category.assoc (unitFamilyMap H X) p.hom q.hom).symm

@[simp]
theorem extendFamilyMap_indexMap {X : NormContinuousSpace K H}
    {Y : Action (AffinoidFamily.{u, v} K) G}
    (f : (localFunctor H).obj X ⟶
      (Action.res (AffinoidFamily.{u, v} K) H.subtype).obj Y)
    (c : G ⧸ H) :
    (extendFamilyMap H f).indexMap c =
      (Y.ρ c.out).indexMap (f.hom.indexMap PUnit.unit) := rfl

/-- The retained pullback is the original input pullback composed with the target's. -/
@[simp]
theorem extendFamilyMap_pullback {X : NormContinuousSpace K H}
    {Y : Action (AffinoidFamily.{u, v} K) G}
    (f : (localFunctor H).obj X ⟶
      (Action.res (AffinoidFamily.{u, v} K) H.subtype).obj Y)
    (c : G ⧸ H) :
    (extendFamilyMap H f).pullback c =
      (f.hom.pullback PUnit.unit).comp
        ((Y.ρ c.out).pullback (f.hom.indexMap PUnit.unit)) := rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.InducedAction
