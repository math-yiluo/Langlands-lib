import Langlands.Algebra.FiniteGaloisOrbits
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.InducedQuotientPointSurjectivityProof
import Langlands.GroupScheme.Torus.InducedRealApproximation
import Langlands.GroupScheme.Torus.RealCharacterNorm
import Langlands.GroupScheme.Torus.RealPermutationLattice
import Langlands.GroupScheme.Torus.RealTorusPoints
import Langlands.GroupScheme.Torus.SurjectionIsogenySectionProof
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Real approximation for rational tori -/

noncomputable section

open CategoryTheory Topology AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj ComplexConjugate

namespace Langlands.GroupScheme.RealTorus

set_option backward.isDefEq.respectTransparency false in
private theorem exists_inducedTorus_with_coordinates
    (k L : Type) [Field k] [Field L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (I : Type) [Finite I] [MulAction (L ≃ₐ[k] L) I] :
    ∃ (P : CommGroupScheme (Spec (CommRingCat.of k)))
      (e : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj P) ≃+ (I → ℤ)),
      IsInducedTorus P ∧ IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj P).toGrp ∧
      ∀ σ χ i, e (characterLattice.galoisRepresentation k L P σ χ) i = e χ (σ⁻¹ • i) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  obtain ⟨n, E, e, he⟩ := Langlands.Algebra.FiniteGaloisOrbits.exists_finite_fields k L (I := I)
  let P := WeilGm.commGroupScheme (CommRingCat.of k) (∀ j, E j)
  let c := (WeilGm.productEmbeddingCharacterEquiv k L E).trans
    (LinearEquiv.piCongrLeft' ℤ (fun _ : Σ j, E j →ₐ[k] L => ℤ) e).toAddEquiv
  have hsplit : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj P).toGrp :=
    ⟨(Σ j, E j →ₐ[k] L), inferInstance,
      ⟨WeilGm.decompositionIso (CommRingCat.of k) (CommRingCat.of L) (∀ j, E j)
        (Σ j, E j →ₐ[k] L) (WeilGm.productEmbeddingDecomposition k L E)⟩⟩
  have hc (σ : L ≃ₐ[k] L) (χ) (i : I) :
      c (characterLattice.galoisRepresentation k L P σ χ) i = c χ (σ⁻¹ • i) := by
    obtain ⟨⟨j, a⟩, rfl⟩ := e.surjective i
    have h := he σ⁻¹ j a
    change (WeilGm.productEmbeddingCharacterEquiv k L E)
      (characterLattice.galoisRepresentation k L P σ χ) (e.symm (e ⟨j, a⟩)) =
      (WeilGm.productEmbeddingCharacterEquiv k L E) χ (e.symm (σ⁻¹ • e ⟨j, a⟩))
    rw [← h, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
      WeilGm.productEmbeddingCharacterEquiv_galoisRepresentation]
    rfl
  refine ⟨P, c, ?_, hsplit, hc⟩
  let b := (Pi.basisFun ℤ I).map c.symm.toIntLinearEquiv
  have hb (i : I) : c (b i) = Pi.basisFun ℤ I i := c.apply_symm_apply _
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, hsplit, I, b, ?_⟩
  intro σ i
  refine ⟨σ • i, c.injective ?_⟩
  funext j
  rw [hc, hb, hb]
  simp only [Pi.basisFun_apply, Pi.single_apply, inv_smul_eq_iff]

private theorem exists_equivariant_lift
    {M I : Type} [AddCommGroup M]
    (s : M ≃+ M) (t : I → I) (ht : Function.Involutive t)
    (f : M →+ (I → ℤ)) (r : (I → ℤ) →+ M) (i : I)
    (hf : ∀ m j, f (s m) j = f m (t j)) (hr : ∀ m, r (f m) = m) (hi : t i = i)
    (x y : Multiplicative M →* ℂˣ)
    (hxy : ∀ m, (x (.ofAdd m) : ℂ) = (-1 : ℂ) ^ f m i * (y (.ofAdd m) : ℂ) *
      conj (y (.ofAdd (s m)) : ℂ)) :
    ∃ z : Multiplicative (I → ℤ) →* ℂˣ,
      (∀ a : I → ℤ, (z (.ofAdd (a ∘ t)) : ℂ) = conj (z (.ofAdd a) : ℂ)) ∧
      (∀ m : M, z (.ofAdd (f m)) = x (.ofAdd m)) := by
  let reindex : (I → ℤ) →+ (I → ℤ) :=
    { toFun := fun a => a ∘ t
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let sign : Multiplicative (I → ℤ) →* ℂˣ :=
    { toFun := fun a => Units.mk0 (-1 : ℂ) (by norm_num) ^ a.toAdd i
      map_one' := zpow_zero _
      map_mul' := fun a b => zpow_add _ (a.toAdd i) (b.toAdd i) }
  let w := y.comp r.toMultiplicative
  let w' := (Units.map (starRingEnd ℂ).toMonoidHom).comp (w.comp reindex.toMultiplicative)
  let z := sign * w * w'
  have hz (a : I → ℤ) : (z (.ofAdd a) : ℂ) =
      (-1 : ℂ) ^ a i * (y (.ofAdd (r a)) : ℂ) * conj (y (.ofAdd (r (a ∘ t))) : ℂ) := by
    change (((Units.mk0 (-1 : ℂ) _) ^ a i : ℂˣ) : ℂ) * (y (.ofAdd (r a)) : ℂ) *
      conj (y (.ofAdd (r (a ∘ t))) : ℂ) = _
    rw [Units.val_zpow_eq_zpow_val, Units.val_mk0]
  refine ⟨z, ?_, ?_⟩
  · intro a
    have haa : (a ∘ t) ∘ t = a := funext fun j => congrArg a (ht j)
    rw [hz, hz, haa, map_mul, map_mul, map_zpow₀, map_neg, map_one]
    simp only [Function.comp_apply, hi, starRingEnd_apply, star_star]
    ac_rfl
  · intro m
    apply Units.ext
    have hsm : f m ∘ t = f (s m) := funext fun j => (hf m j).symm
    rw [hz, hr, hsm, hr, hxy]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 600000 in
private theorem exists_induced_lift
    (T : CommGroupScheme (Spec (CommRingCat.of ℚ))) [IsAffine T.X.left]
    (hT : IsTorus T.toGrp) (p : Lie.AffinePoints T.toGrp ℝ) :
    ∃ (P : CommGroupScheme (Spec (CommRingCat.of ℚ))), IsInducedTorus P ∧
      ∃ (φ : P ⟶ T) (q : Lie.AffinePoints P.toGrp ℝ),
        q ≫ (CommGroupScheme.groupHom φ).hom.hom = p := by
  obtain ⟨L, hL, hA, hfin, hGal, hsplit⟩ := torusFiniteGaloisSplitting ℚ T.toGrp hT
  let := hL
  let := hA
  let := hfin
  let := hGal
  let a : L →ₐ[ℚ] ℂ := IsAlgClosed.lift
  let : Algebra L ℂ := a.toRingHom.toAlgebra
  let : IsScalarTower ℚ L ℂ := IsScalarTower.of_algebraMap_eq fun r => (a.commutes r).symm
  let σ := (Complex.conjAe.restrictScalars ℚ).restrictNormal L
  have hconj (b : L) : algebraMap L ℂ (σ b) = conj (algebraMap L ℂ b) :=
    (Complex.conjAe.restrictScalars ℚ).restrictNormal_commutes L b
  have hσ : σ * σ = 1 := by
    apply AlgEquiv.ext
    intro b
    apply (algebraMap L ℂ).injective
    change algebraMap L ℂ (σ (σ b)) = algebraMap L ℂ b
    rw [hconj, hconj]
    exact star_star _
  have hInv : σ⁻¹ = σ := by
    calc
      σ⁻¹ = σ⁻¹ * (σ * σ) := by rw [hσ, mul_one]
      _ = σ := inv_mul_cancel_left _ _
  let bc := CommGroupScheme.baseChange (algebraBaseMap ℚ L)
  let M := characterLattice (bc.obj T)
  have hTE : IsSplitTorus (bc.obj T).toGrp := hsplit
  obtain ⟨hfree, hfinite⟩ := TorusSurjectionIsogenySection.characterLattice_free_finite hTE
  let : Module.Free ℤ M := hfree
  let : Module.Finite ℤ M := hfinite
  let ρ := characterLattice.galoisRepresentation ℚ L T
  have hρ (m : M) : ρ σ (ρ σ m) = m := by
    rw [← Module.End.mul_apply, ← map_mul, hσ, map_one]
    rfl
  let s : M ≃+ M :=
    { toFun := ρ σ
      invFun := ρ σ
      left_inv := hρ
      right_inv := hρ
      map_add' := map_add _ }
  let pℂ := GaloisPoint.relativeExtend ℚ ℝ ℂ T.toGrp p
  let x : Multiplicative M →* ℂˣ := complexCharacter L T pℂ
  have hx (m : M) : (x (.ofAdd (s m)) : ℂ) = conj (x (.ofAdd m) : ℂ) :=
    complexCharacter_real L T σ hconj p m
  obtain ⟨d, y, hd, hxy⟩ := characterNormDecomposition M s hρ x hx
  obtain ⟨I, hI, hAction, f, r, i, hf, hr, hi, hdi⟩ :=
    permutationLatticeWithFixedCoordinate (L ≃ₐ[ℚ] L) M ρ σ d hd
  let := hI
  let := hAction
  let t : I → I := fun j => σ⁻¹ • j
  have ht : Function.Involutive t := by
    intro j
    change σ⁻¹ • (σ⁻¹ • j) = j
    rw [hInv, ← mul_smul, hσ, one_smul]
  have hi' : t i = i := by
    change σ⁻¹ • i = i
    rw [hInv, hi]
  obtain ⟨z, hz, hzf⟩ := exists_equivariant_lift s t ht f r i (hf σ) hr hi'
    x y (fun m => by rw [hdi]; exact hxy m)
  obtain ⟨P, c, hP, hPE, hc⟩ := exists_inducedTorus_with_coordinates ℚ L I
  let : IsAffine P.X.left := SplittingAssembly.isAffine_of_isTorus P.toGrp hP.isTorus
  let F : M →+ characterLattice (bc.obj P) := c.symm.toAddMonoidHom.comp f
  have hF (m : M) : c (F m) = f m := c.apply_symm_apply _
  have hFgal (g : L ≃ₐ[ℚ] L) (m : M) :
      F (ρ g m) = characterLattice.galoisRepresentation ℚ L P g (F m) := by
    apply c.injective
    funext j
    rw [hF, hc, hF]
    exact hf g m j
  obtain ⟨φ, hφ, _⟩ := hTE.existsUnique_hom_of_equivariant_characterMap F hFgal
  let zP := z.comp c.toAddMonoidHom.toMultiplicative
  have hzP (m : characterLattice (bc.obj P)) :
      (zP (.ofAdd (characterLattice.galoisRepresentation ℚ L P σ m)) : ℂ) =
        conj (zP (.ofAdd m) : ℂ) := by
    change (z (.ofAdd (c (characterLattice.galoisRepresentation ℚ L P σ m))) : ℂ) =
      conj (z (.ofAdd (c m)) : ℂ)
    rw [show c (characterLattice.galoisRepresentation ℚ L P σ m) = c m ∘ t from funext (hc σ m)]
    exact hz _
  obtain ⟨q, hq⟩ := exists_realPoint_of_complexCharacter_equivariant L P σ hconj hPE zP hzP
  refine ⟨P, hP, φ, q, ?_⟩
  apply GaloisPoint.relativeExtend_injective ℚ ℝ ℂ T.toGrp
  apply complexCharacter_injective L T hTE
  have hφext :
      GaloisPoint.relativeExtend ℚ ℝ ℂ T.toGrp (q ≫ (CommGroupScheme.groupHom φ).hom.hom) =
        (GaloisPoint.relativeExtend ℚ ℝ ℂ P.toGrp q) ≫ (CommGroupScheme.groupHom φ).hom.hom :=
    (InducedQuotientPointSurjectivity.affineMap_comp_hom (CommGroupScheme.groupHom φ)
      (IsScalarTower.toAlgHom ℚ ℝ ℂ) q).symm
  apply MonoidHom.ext
  intro χ
  change complexCharacter L T _ (.ofAdd χ.toAdd) = x χ
  rw [hφext, complexCharacter_comp, hφ, hq]
  change z (.ofAdd (c (F χ.toAdd))) = x (.ofAdd χ.toAdd)
  rw [hF, hzf]

end Langlands.GroupScheme.RealTorus

namespace Langlands.GroupScheme

/-- Every affine rational torus has dense rational points in its actual real points. -/
def TorusRealApproximationStatement : Prop :=
  ∀ (T : CommGroupScheme (Spec (CommRingCat.of ℚ))) [IsAffine T.X.left],
    IsTorus T.toGrp → HasRealApproximation T.X

theorem torusRealApproximation : TorusRealApproximationStatement := by
  intro T _ hT p
  obtain ⟨P, hP, φ, q, hq⟩ := RealTorus.exists_induced_lift T hT p
  let : IsAffine P.X.left := SplittingAssembly.isAffine_of_isTorus P.toGrp hP.isTorus
  let F : RingPoint ℚ P.X ℝ → RingPoint ℚ T.X ℝ :=
    fun u => u ≫ (CommGroupScheme.groupHom φ).hom.hom
  have hq' : F q = p := hq
  rw [← hq']
  have hPd := inducedTorusRealApproximation P hP
  have hFc : Continuous F :=
    continuous_affineSchemePointMap ℚ ℝ (CommGroupScheme.groupHom φ).hom.hom
  have hF :
      F '' Set.range (fun r : RingPoint ℚ P.X ℚ => r.changeRing (Algebra.ofId ℚ ℝ)) ⊆
        Set.range (fun r : RingPoint ℚ T.X ℚ => r.changeRing (Algebra.ofId ℚ ℝ)) := by
    rintro _ ⟨_, ⟨r, rfl⟩, rfl⟩
    exact ⟨r ≫ (CommGroupScheme.groupHom φ).hom.hom, (Category.assoc _ _ _).symm⟩
  exact closure_mono hF (image_closure_subset_closure_image hFc ⟨q, hPd q, rfl⟩)

end Langlands.GroupScheme
