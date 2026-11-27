import Langlands.Correspondence.Laumon.FieldMonodromy
import Langlands.Correspondence.Laumon.Completion
import WeilConjectures.RingTheory.InertiaIndEtale
import WeilConjectures.WeilSheaf.BoundaryStrictHenselization

/-!
# Local monodromy at a closed point of a curve

Laumon (1987), (2.2.1), p. 155: for a smooth connected curve `X` over `k` and a closed point
`x`, `G_x` is the Galois group of the henselian trait `X_(x)` and the local monodromy of a sheaf
`F` at `x` is the `G_x`-module `F_η̄`. This module defines the generic monodromy of a lisse sheaf
on a dense open of an integral curve, the decomposition field of a place `Q` of the separable
closure of the function field above a closed point `z` (the fraction field of the henselization
at `z`), and the local monodromy as the monodromy of the pullback to the punctured henselian
neighbourhood. It states the comparison with the generic monodromy, with the Library's inertia
and residue map at a completion, and the description of the stalks of `j_* F` at the geometric
points over the places above `z` as inertia invariants, compatibly with the Galois action that
permutes the places, acting on the stalks through the residue fields.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry.ProEtale Pointwise

namespace Langlands.Henniart.Laumon

open Langlands.Henniart.LocalNumerical

attribute [local instance] Langlands.LocalField.Laurent.valuativeRel

/-- A separable closure of `K` is a separable closure of every intermediate field. -/
instance intermediateField_isSepClosure (K : Type u) [Field K]
    (H : IntermediateField K (SeparableClosure K)) : IsSepClosure H (SeparableClosure K) :=
  ⟨inferInstance, Algebra.isSeparable_tower_top_of_isSeparable K H (SeparableClosure K)⟩

section Curve

variable (C : Scheme.{u}) [IsIntegral C] (U : C.Opens) [Nonempty U]

/-- A nonempty open of an integral scheme contains its generic point. -/
theorem genericPoint_mem_open : genericPoint C ∈ U := by
  obtain ⟨x⟩ := ‹Nonempty U›
  exact ((genericPoint_spec C).mem_open_set_iff U.isOpen).mpr ⟨x.1, trivial, x.2⟩

/-- The generic point `Spec K(C) → U` of a nonempty open `U`. -/
def curveGenericPoint : Spec C.functionField ⟶ U :=
  U.fromSpecStalkOfMem (genericPoint C) (genericPoint_mem_open C U)

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The generic monodromy of a lisse sheaf on `U`: the monodromy of its pullback to the generic
point, a representation of the absolute Galois group of the function field `K(C)` for its
separable closure `SeparableClosure K(C)`. -/
def genericMonodromy (F : ProEtale.LisseSheaf ℓ U) :
    FiniteRepresentation.{0, u, u + 1} (PadicAlgCl ℓ)
      Gal(SeparableClosure C.functionField/C.functionField) :=
  fieldMonodromyRepresentation ℓ C.functionField (SeparableClosure C.functionField)
    (F.upperStar ℓ (curveGenericPoint C U))

variable (W : C.Opens) [Nonempty W]

set_option synthInstance.maxHeartbeats 400000 in
/-- The decomposition field of a prime `Q` of the integral closure of `Γ(C, W)` in the separable
closure of `K(C)`: the fixed field of the stabilizer of `Q`. For `Q` maximal above a closed point
`z`, it is the fraction field of the henselization of the local ring at `z`. -/
def placeDecompositionField
    (Q : Ideal (integralClosure Γ(C, W) (SeparableClosure C.functionField))) :
    IntermediateField C.functionField (SeparableClosure C.functionField) :=
  IntermediateField.fixedField
    (MulAction.stabilizer Gal(SeparableClosure C.functionField/C.functionField) Q)

/-- The punctured henselian neighbourhood `Spec K_Q → Spec K(C) → U` at the place `Q`. -/
def henselianPoint
    (Q : Ideal (integralClosure Γ(C, W) (SeparableClosure C.functionField))) :
    Spec (.of (placeDecompositionField C W Q)) ⟶ U :=
  Spec.map (CommRingCat.ofHom (algebraMap C.functionField (placeDecompositionField C W Q))) ≫
    curveGenericPoint C U

/-- The local monodromy at the place `Q`: the monodromy of the pullback of `F` to the punctured
henselian neighbourhood, a representation of the Galois group of the decomposition field. -/
def boundaryMonodromy (F : ProEtale.LisseSheaf ℓ U)
    (Q : Ideal (integralClosure Γ(C, W) (SeparableClosure C.functionField))) :
    FiniteRepresentation.{0, u, u + 1} (PadicAlgCl ℓ)
      Gal(SeparableClosure C.functionField/placeDecompositionField C W Q) :=
  fieldMonodromyRepresentation ℓ (placeDecompositionField C W Q)
    (SeparableClosure C.functionField) (F.upperStar ℓ (henselianPoint C U W Q))

end Curve

section Place

attribute [local instance] Ideal.Quotient.field

variable (C : Scheme.{u}) [IsIntegral C] (U : C.Opens) [Nonempty U] (ℓ : ℕ) [Fact ℓ.Prime]
  (W : C.Opens) [Nonempty W] (hW : IsAffineOpen W)
  (Q : Ideal (integralClosure Γ(C, W) (SeparableClosure C.functionField))) [Q.IsMaximal]

/-- The geometric point `Spec (B/Q)^alg → Spec Γ(C, W) → C` over the place `Q`, where `B` is the
integral closure of `Γ(C, W)` in the separable closure of the function field. -/
abbrev placeGeometricPoint :
    Spec (.of (AlgebraicClosure
      (integralClosure Γ(C, W) (SeparableClosure C.functionField) ⧸ Q))) ⟶ C :=
  Scheme.FiniteEtale.pointOfAlgebra
    (AlgebraicClosure (integralClosure Γ(C, W) (SeparableClosure C.functionField) ⧸ Q))
    hW.fromSpec

/-- The stalk of `j_* F` at the geometric point over the place `Q`, for the open immersion
`j : U → C`. -/
def placeDirectImageStalk (F : ProEtale.LisseSheaf ℓ U) : ModuleCat.{u + 1} (PadicAlgCl ℓ) :=
  (WeilCoefficients.toModuleCat ℓ).obj ((ProEtale.stalkFunctor ℓ (placeGeometricPoint C W hW Q)).obj
    ((ProEtale.AdicSheaf.forget C).obj ((U.ι)_*ᵃ[ℓ].obj F.obj)))

/-- The transport of the geometric point over the place `Q` to the place `Q'` along a
`Γ(C, W)`-isomorphism `τ'` of the algebraically closed residue fields: `Spec τ'⁻¹` followed by
the point over `Q'` is the point over `Q`. -/
theorem placeGeometricPoint_transport
    (Q' : Ideal (integralClosure Γ(C, W) (SeparableClosure C.functionField))) [Q'.IsMaximal]
    (τ' : AlgebraicClosure (integralClosure Γ(C, W) (SeparableClosure C.functionField) ⧸ Q)
      ≃ₐ[Γ(C, W)]
        AlgebraicClosure (integralClosure Γ(C, W) (SeparableClosure C.functionField) ⧸ Q')) :
    (Scheme.Spec.mapIso τ'.symm.toRingEquiv.toCommRingCatIso.op).hom ≫
        placeGeometricPoint C W hW Q' = placeGeometricPoint C W hW Q := by
  rw [← Category.assoc]
  congr 1
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  ext a
  exact τ'.symm.commutes a

/-- The transport of the stalk of `j_* F` from the geometric point over the place `Q` to the
geometric point over the place `Q'`, along a `Γ(C, W)`-isomorphism `τ'` of the algebraically
closed residue fields: pullback of sections along `Spec τ'`, i.e. the inverse of the
identification of the stalks at a geometric point and at its reparametrization by
`Spec τ'⁻¹`. For `Q' = Q` this is the formula of weil-conjectures's
`AlgebraicGeometry.ProEtale.reparamStalkIso`, which defines the monodromy of lisse sheaves
along `galoisToAut`. -/
def placeStalkTransport
    (Q' : Ideal (integralClosure Γ(C, W) (SeparableClosure C.functionField))) [Q'.IsMaximal]
    (F : ProEtale.LisseSheaf ℓ U)
    (τ' : AlgebraicClosure (integralClosure Γ(C, W) (SeparableClosure C.functionField) ⧸ Q)
      ≃ₐ[Γ(C, W)]
        AlgebraicClosure (integralClosure Γ(C, W) (SeparableClosure C.functionField) ⧸ Q')) :
    placeDirectImageStalk C U ℓ W hW Q F →ₗ[PadicAlgCl ℓ]
      placeDirectImageStalk C U ℓ W hW Q' F :=
  ((WeilCoefficients.toModuleCat ℓ).map
    (eqToHom (congrArg (fun y => (ProEtale.stalkFunctor ℓ y).obj
        ((ProEtale.AdicSheaf.forget C).obj ((U.ι)_*ᵃ[ℓ].obj F.obj)))
      (placeGeometricPoint_transport C W hW Q Q' τ').symm) ≫
    ((Sheaf.Γ _ _).mapIso ((ProEtale.upperStarComp _
        (Scheme.Spec.mapIso τ'.symm.toRingEquiv.toCommRingCatIso.op).hom
        (placeGeometricPoint C W hW Q')).app
        ((ProEtale.AdicSheaf.forget C).obj ((U.ι)_*ᵃ[ℓ].obj F.obj))) ≪≫
      (ProEtale.globalSectionsUpperStarIso _
        (Scheme.Spec.mapIso τ'.symm.toRingEquiv.toCommRingCatIso.op)).app _).hom)).hom

end Place

attribute [local instance] Ideal.Quotient.field in
open Langlands.LocalGalois Langlands.LocalGalois.SepClosed Langlands.Weil.Local.SepClosed in
set_option synthInstance.maxHeartbeats 400000 in
/-- **Local monodromy at a closed point.** For a smooth integral curve over a finite field, a
lisse sheaf on a nonempty open, a closed point `z` and an affine chart around `z`: for every
maximal ideal `Q` of the integral closure of the coordinate ring of the chart in the separable
closure of the function field lying over `z`, the local monodromy is the restriction of the
generic monodromy, and some dense valued embedding of the decomposition field into a Laurent
series field `κ((t))` extends to the separable closures so that Galois restriction is a
topological isomorphism carrying the Library's absolute inertia onto the inertia group of `Q`
and the Library's residue map to the action on the residue field of `Q`, through the reduction
isomorphism induced by the embedding. Moreover, there is a family of embeddings of the stalks of
`j_* F` at the geometric points over these places into the generic stalk, with image the
inertia invariants of the place, compatible with the Galois action: if `τ • Q = Q'` and `τ'`
lifts the residue isomorphism induced by `τ`, then transporting the stalk along `τ'` and
embedding agrees with embedding and applying the generic monodromy of `τ`. For `Q' = Q` this is
the equivariance for the decomposition group, acting on the stalk through its residue action. -/
def BoundaryStalkInertiaStatement : Prop :=
  ∀ (k : Type u) [Field k] [Finite k] (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
  ∀ (C : Scheme.{u}) [C.Over (Spec (.of k))] [IsIntegral C]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (.of k))]
    (U : C.Opens) [Nonempty U] (F : ProEtale.LisseSheaf ℓ U) (z : C), IsClosed ({z} : Set C) →
  ∀ (W : C.Opens) [Nonempty W] (hW : IsAffineOpen W) (hzW : z ∈ W),
    (∀ (Q : Ideal (integralClosure Γ(C, W) (SeparableClosure C.functionField))) [Q.IsMaximal],
      Q.comap (algebraMap Γ(C, W) (integralClosure Γ(C, W) (SeparableClosure C.functionField))) =
        (hW.primeIdealOf ⟨z, hzW⟩).asIdeal →
      Nonempty (FiniteRepresentation.Equiv (boundaryMonodromy C U ℓ W F Q)
        (FiniteRepresentation.restrict (AlgEquiv.restrictScalarsHom C.functionField)
          (genericMonodromy C U ℓ F))) ∧
      ∃ (κ : Type u) (_ : Field κ) (_ : Finite κ)
        (ι₀ : placeDecompositionField C W Q →+* LaurentSeries κ)
        (ι : SeparableClosure C.functionField →+* SeparableClosure (LaurentSeries κ))
        (φ : Gal(SeparableClosure (LaurentSeries κ)/LaurentSeries κ) ≃ₜ*
          Gal(SeparableClosure C.functionField/placeDecompositionField C W Q)),
        DenseRange ι₀ ∧
        (∀ a : placeDecompositionField C W Q,
          ι a = algebraMap (LaurentSeries κ) (SeparableClosure (LaurentSeries κ)) (ι₀ a)) ∧
        (∀ σ a, ι (φ σ a) = σ (ι a)) ∧
        (∀ b : integralClosure Γ(C, W) (SeparableClosure C.functionField),
          closureValuation (LaurentSeries κ) (SeparableClosure (LaurentSeries κ)) (ι b) ≤ 1 ∧
            (b ∈ Q ↔
              closureValuation (LaurentSeries κ) (SeparableClosure (LaurentSeries κ)) (ι b) < 1)) ∧
        (∀ σ, σ ∈ absoluteInertia (LaurentSeries κ) (SeparableClosure (LaurentSeries κ)) ↔
          AlgEquiv.restrictScalarsHom C.functionField (φ σ) ∈
            Q.inertia Gal(SeparableClosure C.functionField/C.functionField)) ∧
        letI := localNormedField (LaurentSeries κ)
        letI := localNormedField_ultrametric (LaurentSeries κ)
        letI := localNormedField_complete (LaurentSeries κ)
        ∃ ψ : (integralClosure Γ(C, W) (SeparableClosure C.functionField) ⧸ Q) ≃+*
            AlgebraicClosure (localResidueField (LaurentSeries κ)),
          (∀ (b : integralClosure Γ(C, W) (SeparableClosure C.functionField))
              (c : closureIntegers (LaurentSeries κ) (SeparableClosure (LaurentSeries κ))),
            (c : SeparableClosure (LaurentSeries κ)) = ι b →
              ψ (Ideal.Quotient.mk Q b) =
                residueClosureEquiv (LaurentSeries κ) (SeparableClosure (LaurentSeries κ))
                  (IsLocalRing.residue _ c)) ∧
          ∀ σ (b b' : integralClosure Γ(C, W) (SeparableClosure C.functionField)),
            (b' : SeparableClosure C.functionField) = φ σ b →
              ψ (Ideal.Quotient.mk Q b') =
                AlgEquiv.toAlgHom
                  (absoluteResidueHom (LaurentSeries κ) (SeparableClosure (LaurentSeries κ)) σ)
                  (ψ (Ideal.Quotient.mk Q b))) ∧
    ∃ f : ∀ (Q : Ideal (integralClosure Γ(C, W) (SeparableClosure C.functionField)))
        [Q.IsMaximal],
        Q.comap (algebraMap Γ(C, W) (integralClosure Γ(C, W) (SeparableClosure C.functionField))) =
          (hW.primeIdealOf ⟨z, hzW⟩).asIdeal →
        (placeDirectImageStalk C U ℓ W hW Q F →ₗ[PadicAlgCl ℓ] genericMonodromy C U ℓ F),
      (∀ (Q : Ideal (integralClosure Γ(C, W) (SeparableClosure C.functionField))) [Q.IsMaximal]
        (hQ : Q.comap
            (algebraMap Γ(C, W) (integralClosure Γ(C, W) (SeparableClosure C.functionField))) =
          (hW.primeIdealOf ⟨z, hzW⟩).asIdeal),
        Function.Injective (f Q hQ) ∧
        ∀ v, v ∈ LinearMap.range (f Q hQ) ↔
          ∀ σ ∈ Q.inertia Gal(SeparableClosure C.functionField/C.functionField),
            (genericMonodromy C U ℓ F).representation σ v = v) ∧
      ∀ (Q Q' : Ideal (integralClosure Γ(C, W) (SeparableClosure C.functionField)))
        [Q.IsMaximal] [Q'.IsMaximal]
        (hQ : Q.comap
            (algebraMap Γ(C, W) (integralClosure Γ(C, W) (SeparableClosure C.functionField))) =
          (hW.primeIdealOf ⟨z, hzW⟩).asIdeal)
        (hQ' : Q'.comap
            (algebraMap Γ(C, W) (integralClosure Γ(C, W) (SeparableClosure C.functionField))) =
          (hW.primeIdealOf ⟨z, hzW⟩).asIdeal)
        (τ : Gal(SeparableClosure C.functionField/C.functionField))
        (τ' : AlgebraicClosure (integralClosure Γ(C, W) (SeparableClosure C.functionField) ⧸ Q)
          ≃ₐ[Γ(C, W)]
            AlgebraicClosure (integralClosure Γ(C, W) (SeparableClosure C.functionField) ⧸ Q')),
        Q' = τ • Q →
        (∀ b : integralClosure Γ(C, W) (SeparableClosure C.functionField),
          τ' (algebraMap _ _ (Ideal.Quotient.mk Q b)) =
            algebraMap _ _ (Ideal.Quotient.mk Q' (τ • b))) →
        ∀ v, f Q' hQ' (placeStalkTransport C U ℓ W hW Q Q' F τ' v) =
          (genericMonodromy C U ℓ F).representation τ (f Q hQ v)

end Langlands.Henniart.Laumon
