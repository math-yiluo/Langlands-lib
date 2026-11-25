/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist

/-!
# The twisting sheaves `𝒪(m)` on projective space

The projective space `ℙ(n; S)` is the base change to `S` of the integral model
`Proj.projectiveSpaceOverAffine n (ULift ℤ) = Proj ℤ[Tᵢ]`, and `ProjectiveSpace.toProjInt` is
the projection to it. The twisting sheaf `𝒪(m)` on `ℙ(n; S)` is the pullback along this
projection of the twisting sheaf `Proj.twist` of the integral model.

## Main definitions

- `AlgebraicGeometry.ProjectiveSpace.twist`: the twisting sheaf `𝒪(m)` on `ℙ(n; S)`.
- `AlgebraicGeometry.ProjectiveSpace.twistRestrict`: the pullback `i^* 𝒪(m)` of `𝒪(m)` along a
  morphism `i : X ⟶ ℙ(n; S)`.

## Main results

- `AlgebraicGeometry.Proj.isInvertible_twist_homogeneousSubmodule`: `𝒪(m)` is invertible on
  `Proj R[Tᵢ]`.
- `AlgebraicGeometry.ProjectiveSpace.unitIsoTwistZero`: `𝒪(0)` is the structure sheaf.
- `AlgebraicGeometry.ProjectiveSpace.isInvertible_twist`: `𝒪(m)` is invertible on `ℙ(n; S)`.
- `AlgebraicGeometry.ProjectiveSpace.nonempty_tensorObj_twist_iso`: `𝒪(a) ⊗ 𝒪(b) ≅ 𝒪(a + b)`.
- `AlgebraicGeometry.ProjectiveSpace.pullbackMapTwistIso`: `𝒪(m)` commutes with base change.
- `AlgebraicGeometry.ProjectiveSpace.nonempty_tensorPow_twist_one_iso`: `𝒪(1)^{⊗ t} ≅ 𝒪(t)`.
- `AlgebraicGeometry.Proj.epi_sigmaUnitToTwist` and
  `AlgebraicGeometry.ProjectiveSpace.generatingSectionsTwist`: for `d ≥ 0`, `𝒪(d)` is generated
  by the global sections `T_j ^ d`.

## TODO

- Identify `ℙ(n; Spec A)` with `Proj.projectiveSpaceOverAffine n A`, and under this
  identification `twist n (Spec A) m` with `Proj.twist (homogeneousSubmodule n A) m`. This is
  what is needed to compute the cohomology of `𝒪(m)` over a field.

## Implementation details

`toProjInt` is the top arrow of the defining base-change square of `ℙ(n; S)` over `Spec ℤ`, and
it commutes with `map n f` for any `f : S ⟶ T`, so `𝒪(m)` commutes with base change. On the
standard opens `Uᵢ = D₊(xᵢ)`, `𝒪(m)` is free of rank one and glued along the transition units
`ProjectiveSpace.transitionUnit`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

noncomputable section

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

variable (n : Type u)

/-- The standard opens `D₊(Tᵢ)` cover `Proj R[Tᵢ]`, and `Tᵢ` has degree `1`. -/
lemma Proj.exists_mem_basicOpen_homogeneousSubmodule (R : Type u) [CommRing R]
    (x : Proj (MvPolynomial.homogeneousSubmodule n R)) :
    ∃ f ∈ MvPolynomial.homogeneousSubmodule n R 1,
      x ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule n R) f := by
  have h := Proj.iSup_basicOpen_eq_top' (MvPolynomial.homogeneousSubmodule n R)
    (MvPolynomial.X : n → MvPolynomial n R) (fun i ↦ ⟨1, MvPolynomial.isHomogeneous_X R i⟩)
    (MvPolynomial.adjoin_range_X_eq_top n R)
  have hx : x ∈ ⨆ i, Proj.basicOpen (MvPolynomial.homogeneousSubmodule n R)
      (MvPolynomial.X i) := by
    rw [h]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨_, MvPolynomial.isHomogeneous_X R i, hi⟩

/-- **`𝒪(m)` is invertible on `Proj R[Tᵢ]`**: the standard opens `D₊(Tᵢ)` cover `Proj R[Tᵢ]`
and `Tᵢ` has degree `1`. No finiteness of `n` is needed. -/
instance Proj.isInvertible_twist_homogeneousSubmodule (R : Type u) [CommRing R] (m : ℤ) :
    (Proj.twist (MvPolynomial.homogeneousSubmodule n R) m).IsInvertible :=
  Proj.isInvertible_twist _ m (Proj.exists_mem_basicOpen_homogeneousSubmodule n R)

namespace ProjectiveSpace

variable (S : Scheme.{u})

/-- **The twisting sheaf `𝒪(m)` on `ℙ(n; S)`**: the pullback along the projection
`toProjInt: ℙ(n; S) ⟶ Proj ℤ[Tᵢ]` of the twisting sheaf `𝒪(m)` of the integral model. -/
def twist (m : ℤ) : (ℙ(n; S)).Modules :=
  (Scheme.Modules.pullback (toProjInt n S)).obj
    (Proj.twist (MvPolynomial.homogeneousSubmodule n (ULift.{u} ℤ)) m)

lemma twist_def (m : ℤ) :
    twist n S m = (Scheme.Modules.pullback (toProjInt n S)).obj
      (Proj.twist (MvPolynomial.homogeneousSubmodule n (ULift.{u} ℤ)) m) :=
  rfl


/-- **`𝒪(0)` is the structure sheaf** of `ℙ(n; S)`. -/
def unitIsoTwistZero : SheafOfModules.unit (ℙ(n; S)).ringCatSheaf ≅ twist n S 0 :=
  (Scheme.Modules.pullbackObjUnitIso (toProjInt n S)).symm ≪≫
    (Scheme.Modules.pullback (toProjInt n S)).mapIso Proj.unitIsoTwistZero

/-- The morphism `⊕_{j} 𝒪 ⟶ 𝒪(d)` on `Proj R[Tᵢ]`, for `d ≥ 0`, whose `j`-th component is the
global section `T_j ^ d` of `𝒪(d)`, i.e. multiplication by `T_j ^ d` from `𝒪 ≅ 𝒪(0)`. -/
noncomputable def Proj.sigmaUnitToTwist (R : Type u) [CommRing R] (d : ℕ) :
    SheafOfModules.free (R := (Proj (MvPolynomial.homogeneousSubmodule n R)).ringCatSheaf) n ⟶
      Proj.twist (MvPolynomial.homogeneousSubmodule n R) d :=
  Limits.Sigma.desc fun j ↦ Proj.unitToTwistZero ≫
    Proj.twistMul 0 (d := d) (f := MvPolynomial.X j ^ d)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).2 (by
        simpa using (MvPolynomial.isHomogeneous_X R j).pow d)) ≫ eqToHom (by simp)

/-- **`𝒪(d)` is generated by its global sections `T_j ^ d`** on `Proj R[Tᵢ]`, for `d ≥ 0`: on
the standard open `D₊(T_j)`, multiplication by `T_j ^ d` is an isomorphism `𝒪 ≅ 𝒪(d)`, and
these opens cover `Proj R[Tᵢ]`; so `⊕_{j} 𝒪 ⟶ 𝒪(d)` is surjective on stalks. -/
instance Proj.epi_sigmaUnitToTwist (R : Type u) [CommRing R] (d : ℕ) :
    Epi (Proj.sigmaUnitToTwist n R d) := by
  refine Scheme.Modules.epi_of_surjective_stalk _ fun x ↦ ?_
  have hx : x ∈ ⨆ j, Proj.basicOpen (MvPolynomial.homogeneousSubmodule n R)
      (MvPolynomial.X j) := by
    rw [Proj.iSup_basicOpen_eq_top' (MvPolynomial.homogeneousSubmodule n R)
      (MvPolynomial.X : n → MvPolynomial n R) (fun i ↦ ⟨1, MvPolynomial.isHomogeneous_X R i⟩)
      (MvPolynomial.adjoin_range_X_eq_top n R)]
    trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  have hj' : x ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule n R)
      (MvPolynomial.X j ^ d) :=
    (Proj.mem_basicOpen _ _ _).2 fun h ↦
      (Proj.mem_basicOpen _ _ _).1 hj (x.isPrime.mem_of_pow_mem d h)
  have : IsIso ((Scheme.Modules.restrictFunctor
      (Proj.basicOpen _ (MvPolynomial.X j ^ d)).ι).map
        (SheafOfModules.ιFree j ≫ Proj.sigmaUnitToTwist n R d)) := by
    rw [Proj.sigmaUnitToTwist, SheafOfModules.ιFree, Limits.Sigma.ι_comp_desc, Functor.map_comp,
      Functor.map_comp]
    have : IsIso ((Scheme.Modules.restrictFunctor
        (Proj.basicOpen _ (MvPolynomial.X j ^ d)).ι).map
          (Proj.unitToTwistZero (𝒜 := MvPolynomial.homogeneousSubmodule n R))) :=
      ((Scheme.Modules.restrictFunctor (Proj.basicOpen _ (MvPolynomial.X j ^ d)).ι).mapIso
        (Proj.unitIsoTwistZero (𝒜 := MvPolynomial.homogeneousSubmodule n R))).isIso_hom
    infer_instance
  have hb := Scheme.Modules.bijective_stalk_of_isIso_restrict
    (SheafOfModules.ιFree j ≫ Proj.sigmaUnitToTwist n R d) x hj'
  intro z
  obtain ⟨w, hw⟩ := hb.2 z
  exact ⟨_, by rwa [Functor.map_comp, Functor.map_comp, ConcreteCategory.comp_apply] at hw⟩

/-- **`𝒪(m)` is invertible** on `ℙ(n; S)`, being the pullback of an invertible module. -/
instance isInvertible_twist (m : ℤ) : (twist n S m).IsInvertible :=
  Scheme.Modules.IsInvertible.pullback (toProjInt n S)
    (Proj.twist (MvPolynomial.homogeneousSubmodule n (ULift.{u} ℤ)) m)

open MonoidalCategory in
/-- **Twists and tensor products** on `ℙ(n; S)`: `𝒪(a) ⊗ 𝒪(b) ≅ 𝒪(a + b)`, by pulling back the
corresponding isomorphism `Proj.nonempty_tensorObj_twist_iso` of the integral model, the pullback
of a tensor product being the tensor product of the pullbacks. -/
theorem nonempty_tensorObj_twist_iso (a b : ℤ) :
    Nonempty (twist n S a ⊗ twist n S b ≅ twist n S (a + b)) := by
  obtain ⟨e₁⟩ := Scheme.Modules.nonempty_pullback_tensorObj_iso (toProjInt n S)
    (Proj.twist (MvPolynomial.homogeneousSubmodule n (ULift.{u} ℤ)) a)
    (Proj.twist (MvPolynomial.homogeneousSubmodule n (ULift.{u} ℤ)) b)
  obtain ⟨e₂⟩ := Proj.nonempty_tensorObj_twist_iso _
    (Proj.exists_mem_basicOpen_homogeneousSubmodule n (ULift.{u} ℤ)) a b
  exact ⟨e₁.symm ≪≫ (Scheme.Modules.pullback (toProjInt n S)).mapIso e₂⟩

/-- **`𝒪(m)` commutes with base change**: for `f : S ⟶ T`, the pullback of `𝒪(m)` on
`ℙ(n; T)` along `map n f` is `𝒪(m)` on `ℙ(n; S)`. -/
def pullbackMapTwistIso {S T : Scheme.{u}} (f : S ⟶ T) (m : ℤ) :
    (Scheme.Modules.pullback (map n f)).obj (twist n T m) ≅ twist n S m :=
  (Scheme.Modules.pullbackComp (map n f) (toProjInt n T)).app _ ≪≫
    (Scheme.Modules.pullbackCongr (map_toProjInt n f)).app _

/-- **`𝒪(1)^{⊗ t} ≅ 𝒪(t)`** on `ℙ(n; S)`, by induction from `nonempty_tensorObj_twist_iso`. -/
theorem nonempty_tensorPow_twist_one_iso (t : ℕ) :
    Nonempty ((twist n S 1).tensorPow t ≅ twist n S t) := by
  induction t with
  | zero => exact ⟨unitIsoTwistZero n S⟩
  | succ t ih =>
    obtain ⟨e⟩ := nonempty_tensorObj_twist_iso n S 1 t
    exact ⟨(Iso.refl _ ⊗ᵢ ih.some) ≪≫ e ≪≫ eqToIso (by rw [add_comm]; push_cast; rfl)⟩

/-- **`𝒪(d)` is generated by its global sections** on `ℙ(n; S)` for `d ≥ 0`, namely by the
pullbacks of the sections `T_j ^ d` of `Proj.epi_sigmaUnitToTwist`. -/
noncomputable def generatingSectionsTwist (d : ℕ) :
    SheafOfModules.GeneratingSections (twist n S d) :=
  have : @Epi (SheafOfModules _) _ _ _ (Proj.sigmaUnitToTwist n (ULift.{u} ℤ) d) :=
    Proj.epi_sigmaUnitToTwist n _ d
  Scheme.Modules.GeneratingSections.pullback (toProjInt n S)
    (.ofEpiFree (Proj.sigmaUnitToTwist n (ULift.{u} ℤ) d))

variable {n S} {X : Scheme.{u}}

/-- The pullback `𝒪_X(m) = i^* 𝒪(m)` of the twisting sheaf along a morphism
`i : X ⟶ ℙ(n; S)`, e.g. its restriction to a closed subscheme. -/
abbrev twistRestrict (i : X ⟶ ℙ(n; S)) (m : ℤ) : X.Modules :=
  (Scheme.Modules.pullback i).obj (twist n S m)

section Sections

open Scheme.Modules
open MvPolynomial (homogeneousSubmodule X_mem_homogeneousSubmodule_one awayXRatio)

variable (n S) in
/-- **The global section `Tᵢ` of `𝒪(1)`** on `ℙ(n; S)`: the pullback of the global section
`Tᵢ` of `𝒪(1)` on the integral model `Proj ℤ[Tᵢ]`. -/
def twistOneSection (i : n) : Γ(twist n S 1, ⊤) :=
  pullbackSection (toProjInt n S)
    (Hom.app (Proj.unitToTwist (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) i)) ⊤
      (1 : Γ(Proj (homogeneousSubmodule n (ULift.{u} ℤ)), ⊤)))

/-- The pullback of the global section `Tᵢ` of `𝒪(1)` along a morphism `g : X ⟶ ℙ(n; S)` is a
free generator of `g^* 𝒪(1)` over the preimage of the standard open `D₊(Tᵢ)`. -/
lemma isFreeGenerator_pullbackSection_twistOneSection (g : X ⟶ ℙ(n; S)) (i : n) :
    IsFreeGenerator (((Scheme.Modules.pullback g).obj (twist n S 1)).presheaf.map
      (homOfLE (g.preimage_mono (le_top : toProjInt n S ⁻¹ᵁ
        Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (MvPolynomial.X i) ≤ ⊤))).op
      (pullbackSection g (twistOneSection n S i))) := by
  have := isIso_restrictFunctor_map_pullbackObjUnitIso_inv_comp
    (Proj.unitToTwist (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) i)) (g := toProjInt n S)
    (U := Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (MvPolynomial.X i))
  have h := pullbackSection_app_one (toProjInt n S)
    (Proj.unitToTwist (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) i))
  rw [twistOneSection]
  erw [h]
  exact isFreeGenerator_pullbackSection _

/-- **The transition rule** `Tᵢ = (Tᵢ / Tⱼ) • Tⱼ` over `D₊(Tⱼ)`, pulled back along a morphism
`g : X ⟶ ℙ(n; S)`. -/
lemma pullbackSection_twistOneSection_map_eq_smul (g : X ⟶ ℙ(n; S)) (i j : n) :
    ((Scheme.Modules.pullback g).obj (twist n S 1)).presheaf.map
        (homOfLE (g.preimage_mono (le_top : toProjInt n S ⁻¹ᵁ
          Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (MvPolynomial.X j) ≤ ⊤))).op
        (pullbackSection g (twistOneSection n S i)) =
      g.app (toProjInt n S ⁻¹ᵁ
          Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (MvPolynomial.X j))
        ((toProjInt n S).app
          (Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (MvPolynomial.X j))
          (Proj.awayToSection _ _ (awayXRatio (ULift.{u} ℤ) j i))) •
        ((Scheme.Modules.pullback g).obj (twist n S 1)).presheaf.map
          (homOfLE (g.preimage_mono (le_top : toProjInt n S ⁻¹ᵁ
            Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (MvPolynomial.X j) ≤ ⊤))).op
          (pullbackSection g (twistOneSection n S j)) := by
  have H := Proj.map_unitToTwist_eq_smul
    (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) i)
    (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) j)
    (by simpa using X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) i)
  have H₁ := pullbackSection_map_eq_smul (toProjInt n S) le_top H
  exact pullbackSection_map_eq_smul g _ H₁

end Sections

end ProjectiveSpace

end AlgebraicGeometry
