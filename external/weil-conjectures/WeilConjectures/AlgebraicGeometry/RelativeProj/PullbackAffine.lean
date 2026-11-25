/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange
public import WeilConjectures.AlgebraicGeometry.RelativeProj.GradedTensor

/-!
# Pullback of a quasi-coherent graded algebra over an affine base

Let `X` be an affine scheme, `A` a quasi-coherent graded algebra on `X` and `g: X' ⟶ X` any
morphism. We construct the coefficientwise pullback `g^* A` on `X'`,
`(g^* A)(U') = Γ(X', U') ⊗_{Γ(X, ⊤)} A(X)` with the base-changed grading, together with
the identification `PullbackData g A (g^* A)`. Hence the base change theorem
`AlgebraicGeometry.Scheme.GradedAlgebraData.PullbackData.isPullback` applies:
`Proj_{X'}(g^* A) ≅ X' ×_X Proj_X(A)`.

## Main definitions

- `AlgebraicGeometry.Scheme.GradedAlgebraData.pullbackOfIsAffine` — the pullback `g^* A`.
- `AlgebraicGeometry.Scheme.GradedAlgebraData.pullbackDataOfIsAffine` — its identification with
  the coefficientwise pullback.
-/

@[expose] public section

universe u

open CategoryTheory TensorProduct

namespace AlgebraicGeometry.Scheme.GradedAlgebraData

variable {X X' : Scheme.{u}} [IsAffine X] (g : X' ⟶ X) (A : X.GradedAlgebraData)

/-- The whole of an affine scheme, as an affine open. -/
def topAffine (X : Scheme.{u}) [IsAffine X] : X.affineOpens :=
  ⟨⊤, isAffineOpen_top X⟩

/-- The ring `Γ(X', U')`, regarded as a `Γ(X, ⊤)`-algebra via `g`. -/
@[nolint unusedArguments]
def PullbackRing (_ : X' ⟶ X) (U' : X'.affineOpens) : Type u :=
  Γ(X', U'.1)

instance (U' : X'.affineOpens) : CommRing (PullbackRing g U') :=
  inferInstanceAs (CommRing Γ(X', U'.1))

noncomputable instance (U' : X'.affineOpens) : Algebra Γ(X, (topAffine X).1) (PullbackRing g U') :=
  (g.appLE (topAffine X).1 U'.1 le_top).hom.toAlgebra

lemma algebraMap_pullbackRing (U' : X'.affineOpens) :
    algebraMap Γ(X, (topAffine X).1) (PullbackRing g U') =
      (g.appLE (topAffine X).1 U'.1 le_top).hom :=
  rfl

/-- The restriction maps of the rings `PullbackRing g U'`, as `Γ(X, ⊤)`-algebra maps. -/
noncomputable def pullbackRingRes {U' V' : X'.affineOpens} (h : U' ≤ V') :
    PullbackRing g V' →ₐ[Γ(X, (topAffine X).1)] PullbackRing g U' where
  __ := (X'.presheaf.map (homOfLE (X := X'.Opens) h).op).hom
  commutes' r := by
    change (g.appLE (topAffine X).1 V'.1 le_top ≫
      X'.presheaf.map (homOfLE (X := X'.Opens) h).op).hom r = _
    rw [Scheme.Hom.appLE_map]
    rfl

lemma pullbackRingRes_apply {U' V' : X'.affineOpens} (h : U' ≤ V') (x : PullbackRing g V') :
    pullbackRingRes g h x = (X'.presheaf.map (homOfLE (X := X'.Opens) h).op).hom x :=
  rfl

/-- The coefficientwise pullback of a quasi-coherent graded algebra along a morphism to an affine
scheme: `(g^* A)(U') = Γ(X', U') ⊗_{Γ(X, ⊤)} A(X)`. -/
noncomputable def pullbackOfIsAffine : X'.GradedAlgebraData where
  obj U' := PullbackRing g U' ⊗[Γ(X, (topAffine X).1)] A.obj (topAffine X)
  commRing U' := inferInstance
  algebra U' := inferInstanceAs (Algebra (PullbackRing g U') _)
  grading U' n := (A.grading (topAffine X) n).baseChange (PullbackRing g U')
  gradedAlgebra U' := GradedAlgebra.baseChange (S := PullbackRing g U') (A.grading (topAffine X))
  res {U' V'} h := GradedRingHom.baseChangeMap (A.grading (topAffine X)) (pullbackRingRes g h)
  res_id U' x := by
    induction x using TensorProduct.inductionOn with
    | tmul t a =>
      change pullbackRingRes g le_rfl t ⊗ₜ a = t ⊗ₜ a
      rw [pullbackRingRes_apply, show homOfLE (X := X'.Opens) (le_refl U'.1) = 𝟙 _ from
        Subsingleton.elim _ _, op_id, X'.presheaf.map_id]
      rfl
    | add x y hx hy => exact (map_add _ _ _).trans (congrArg₂ _ hx hy)
  res_res {U' V' W'} h₁ h₂ x := by
    induction x using TensorProduct.inductionOn with
    | tmul t a =>
      change pullbackRingRes g h₁ (pullbackRingRes g h₂ t) ⊗ₜ a =
        pullbackRingRes g (h₁.trans h₂) t ⊗ₜ a
      rw [pullbackRingRes_apply, pullbackRingRes_apply, pullbackRingRes_apply,
        ← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  isGradedBaseChangeAlong {U' V'} h := by
    let : Algebra (PullbackRing g V') (PullbackRing g U') :=
      (pullbackRingRes g h).toRingHom.toAlgebra
    have : IsScalarTower Γ(X, (topAffine X).1) (PullbackRing g V') (PullbackRing g U') :=
      .of_algebraMap_eq fun r ↦ ((pullbackRingRes g h).commutes r).symm
    have key := GradedRingHom.isGradedBaseChange_baseChangeMap (A.grading (topAffine X))
      (T := PullbackRing g V') (T' := PullbackRing g U')
    have e : IsScalarTower.toAlgHom _ (PullbackRing g V') (PullbackRing g U') =
        pullbackRingRes g h := AlgHom.ext fun _ ↦ rfl
    rw [e] at key
    exact GradedRingHom.isGradedBaseChangeAlong_algebraMap_iff.mpr key

lemma le_topAffine (U : X.affineOpens) : U ≤ topAffine X :=
  le_top (a := U.1)

/-- The `Γ(X, ⊤)`-algebra structure on `Γ(X, U)`. -/
@[reducible] noncomputable def algebraTopAffine (U : X.affineOpens) :
    Algebra Γ(X, (topAffine X).1) Γ(X, U.1) :=
  (X.presheaf.map (homOfLE (X := X.Opens) (le_topAffine U)).op).hom.toAlgebra

/-- The `Γ(X, ⊤)`-algebra structure on `A(U)`. -/
@[reducible] noncomputable def algebraTopAffineObj (U : X.affineOpens) :
    Algebra Γ(X, (topAffine X).1) (A.obj U) :=
  letI := algebraTopAffine U
  ((algebraMap Γ(X, U.1) (A.obj U)).comp (algebraMap Γ(X, (topAffine X).1) Γ(X, U.1))).toAlgebra

/-- The `Γ(X, U)`-algebra structure on `Γ(X', U')` for `U' ⊆ g⁻¹ U`. -/
@[reducible] noncomputable def algebraPullbackRing {U' : X'.affineOpens} {U : X.affineOpens}
    (h : U'.1 ≤ g ⁻¹ᵁ U.1) : Algebra Γ(X, U.1) (PullbackRing g U') :=
  (g.appLE U.1 U'.1 h).hom.toAlgebra

omit [IsAffine X] in
lemma appLE_res_apply {U' : X'.affineOpens} {U V : X.affineOpens} (h : U'.1 ≤ g ⁻¹ᵁ U.1)
    (hUV : U ≤ V) (r : Γ(X, V.1)) :
    (g.appLE U.1 U'.1 h).hom ((X.presheaf.map (homOfLE (X := X.Opens) hUV).op).hom r) =
      (g.appLE V.1 U'.1 (h.trans (g.preimage_mono hUV))).hom r := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

omit [IsAffine X] in
lemma res_appLE_apply {U' V' : X'.affineOpens} {U : X.affineOpens} (h' : U' ≤ V')
    (h : V'.1 ≤ g ⁻¹ᵁ U.1) (r : Γ(X, U.1)) :
    (X'.presheaf.map (homOfLE (X := X'.Opens) h').op).hom ((g.appLE U.1 V'.1 h).hom r) =
      (g.appLE U.1 U'.1 ((show U'.1 ≤ V'.1 from h').trans h)).hom r := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

lemma isGradedBaseChange_res_topAffine (U : X.affineOpens) :
    letI := algebraTopAffine U
    letI := algebraTopAffineObj A U
    haveI : IsScalarTower Γ(X, (topAffine X).1) Γ(X, U.1) (A.obj U) := .of_algebraMap_eq' rfl
    (A.res (le_topAffine U)).IsGradedBaseChange := by
  let := algebraTopAffine U
  let := algebraTopAffineObj A U
  have : IsScalarTower Γ(X, (topAffine X).1) Γ(X, U.1) (A.obj U) := .of_algebraMap_eq' rfl
  exact GradedRingHom.isGradedBaseChangeAlong_algebraMap_iff.mp (A.isGradedBaseChangeAlong _)

/-- The comparison map `A(U) → Γ(X', U') ⊗_{Γ(X, ⊤)} A(X)` for `U' ⊆ g⁻¹ U`. -/
noncomputable def pullbackMap {U' : X'.affineOpens} {U : X.affineOpens} (h : U'.1 ≤ g ⁻¹ᵁ U.1) :
    A.grading U →+*ᵍ (A.pullbackOfIsAffine g).grading U' :=
  letI := algebraTopAffine U
  letI := algebraTopAffineObj A U
  haveI : IsScalarTower Γ(X, (topAffine X).1) Γ(X, U.1) (A.obj U) := .of_algebraMap_eq' rfl
  letI := algebraPullbackRing g h
  haveI : IsScalarTower Γ(X, (topAffine X).1) Γ(X, U.1) (PullbackRing g U') :=
    .of_algebraMap_eq fun r ↦ (appLE_res_apply g h (le_topAffine U) r).symm
  (A.isGradedBaseChange_res_topAffine U).lift (PullbackRing g U')

lemma pullbackMap_res {U' : X'.affineOpens} {U : X.affineOpens} (h : U'.1 ≤ g ⁻¹ᵁ U.1)
    (a : A.obj (topAffine X)) :
    A.pullbackMap g h (A.res (le_topAffine U) a) = (1 : PullbackRing g U') ⊗ₜ a :=
  letI := algebraTopAffine U
  letI := algebraTopAffineObj A U
  haveI : IsScalarTower Γ(X, (topAffine X).1) Γ(X, U.1) (A.obj U) := .of_algebraMap_eq' rfl
  letI := algebraPullbackRing g h
  haveI : IsScalarTower Γ(X, (topAffine X).1) Γ(X, U.1) (PullbackRing g U') :=
    .of_algebraMap_eq fun r ↦ (appLE_res_apply g h (le_topAffine U) r).symm
  (A.isGradedBaseChange_res_topAffine U).liftAlgHom_apply (PullbackRing g U') a

lemma pullbackMap_algebraMap {U' : X'.affineOpens} {U : X.affineOpens} (h : U'.1 ≤ g ⁻¹ᵁ U.1)
    (s : Γ(X, U.1)) :
    A.pullbackMap g h (algebraMap _ _ s) =
      TensorProduct.tmul (M := PullbackRing g U') _ ((g.appLE U.1 U'.1 h).hom s)
        (1 : A.obj (topAffine X)) :=
  letI := algebraTopAffine U
  letI := algebraTopAffineObj A U
  haveI : IsScalarTower Γ(X, (topAffine X).1) Γ(X, U.1) (A.obj U) := .of_algebraMap_eq' rfl
  letI := algebraPullbackRing g h
  haveI : IsScalarTower Γ(X, (topAffine X).1) Γ(X, U.1) (PullbackRing g U') :=
    .of_algebraMap_eq fun r ↦ (appLE_res_apply g h (le_topAffine U) r).symm
  (A.isGradedBaseChange_res_topAffine U).liftAlgHom_algebraMap (PullbackRing g U') s

lemma isGradedBaseChangeAlong_pullbackMap {U' : X'.affineOpens} {U : X.affineOpens}
    (h : U'.1 ≤ g ⁻¹ᵁ U.1) :
    (A.pullbackMap g h).IsGradedBaseChangeAlong (g.appLE U.1 U'.1 h).hom := by
  let := algebraTopAffine U
  let := algebraTopAffineObj A U
  have : IsScalarTower Γ(X, (topAffine X).1) Γ(X, U.1) (A.obj U) := .of_algebraMap_eq' rfl
  let := algebraPullbackRing g h
  have : IsScalarTower Γ(X, (topAffine X).1) Γ(X, U.1) (PullbackRing g U') :=
    .of_algebraMap_eq fun r ↦ (appLE_res_apply g h (le_topAffine U) r).symm
  exact GradedRingHom.isGradedBaseChangeAlong_algebraMap_iff.mpr
    ((A.isGradedBaseChange_res_topAffine U).isGradedBaseChange_lift (PullbackRing g U'))

lemma res_pullbackMap {U' V' : X'.affineOpens} {U : X.affineOpens} (h' : U' ≤ V')
    (h : V'.1 ≤ g ⁻¹ᵁ U.1) (x : A.obj U) :
    (A.pullbackOfIsAffine g).res h' (A.pullbackMap g h x) =
      A.pullbackMap g ((show U'.1 ≤ V'.1 from h').trans h) x := by
  let := algebraTopAffine U
  let := algebraTopAffineObj A U
  have : IsScalarTower Γ(X, (topAffine X).1) Γ(X, U.1) (A.obj U) := .of_algebraMap_eq' rfl
  have key := (A.isGradedBaseChange_res_topAffine U).ringHom_ext
    (u := ((A.pullbackOfIsAffine g).res h').toRingHom.comp (A.pullbackMap g h).toRingHom)
    (v := (A.pullbackMap g ((show U'.1 ≤ V'.1 from h').trans h)).toRingHom) ?_ ?_
  · exact RingHom.congr_fun key x
  · intro a
    change (A.pullbackOfIsAffine g).res h' (A.pullbackMap g h (A.res _ a)) =
      A.pullbackMap g _ (A.res _ a)
    rw [pullbackMap_res, pullbackMap_res]
    change pullbackRingRes g h' 1 ⊗ₜ a = _
    rw [map_one]
  · intro s
    change (A.pullbackOfIsAffine g).res h' (A.pullbackMap g h (algebraMap _ _ s)) =
      A.pullbackMap g _ (algebraMap _ _ s)
    rw [pullbackMap_algebraMap, pullbackMap_algebraMap]
    change pullbackRingRes g h' _ ⊗ₜ _ = _
    rw [pullbackRingRes_apply, res_appLE_apply]
    rfl

lemma pullbackMap_res_res {U' : X'.affineOpens} {U V : X.affineOpens} (h : U'.1 ≤ g ⁻¹ᵁ U.1)
    (hUV : U ≤ V) (x : A.obj V) :
    A.pullbackMap g h (A.res hUV x) = A.pullbackMap g (h.trans (g.preimage_mono hUV)) x := by
  let := algebraTopAffine V
  let := algebraTopAffineObj A V
  have : IsScalarTower Γ(X, (topAffine X).1) Γ(X, V.1) (A.obj V) := .of_algebraMap_eq' rfl
  have key := (A.isGradedBaseChange_res_topAffine V).ringHom_ext
    (u := (A.pullbackMap g h).toRingHom.comp (A.res hUV).toRingHom)
    (v := (A.pullbackMap g (h.trans (g.preimage_mono hUV))).toRingHom) ?_ ?_
  · exact RingHom.congr_fun key x
  · intro a
    change A.pullbackMap g h (A.res hUV (A.res _ a)) = A.pullbackMap g _ (A.res _ a)
    rw [A.res_res, pullbackMap_res, pullbackMap_res]
  · intro s
    change A.pullbackMap g h (A.res hUV (algebraMap _ _ s)) = A.pullbackMap g _ (algebraMap _ _ s)
    rw [A.res_algebraMap, pullbackMap_algebraMap, pullbackMap_algebraMap, appLE_res_apply]

/-- The pullback `g^* A` of a quasi-coherent graded algebra along a morphism to an affine scheme
is identified with the coefficientwise pullback of `A`; in particular `PullbackData` is not
vacuous. -/
noncomputable def pullbackDataOfIsAffine : PullbackData g A (A.pullbackOfIsAffine g) where
  map h := A.pullbackMap g h
  isGradedBaseChangeAlong h := A.isGradedBaseChangeAlong_pullbackMap g h
  res_map h' h x := A.res_pullbackMap g h' h x
  map_res h hUV x := A.pullbackMap_res_res g h hUV x

/-- **Base change of relative `Proj` over an affine base**: for `X` affine and any
`g: X' ⟶ X`, `Proj_{X'}(g^* A) ≅ X' ×_X Proj_X(A)`. -/
theorem isPullback_pullbackOfIsAffine :
    IsPullback (A.pullbackDataOfIsAffine g).relProjComparison
      (A.pullbackOfIsAffine g).relProjHom A.relProjHom g :=
  (A.pullbackDataOfIsAffine g).isPullback

end AlgebraicGeometry.Scheme.GradedAlgebraData
