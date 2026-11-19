import Langlands.Global.AdelicNormOneQuotientClosedEmbedding
import Langlands.Global.AdelicClosedSubgroupHeightChain
import Langlands.Global.AdelicLineCharacterHeight
import Langlands.Global.AdelicPositiveImageClosed

/-! # Closed embeddings of actual norm-one rational quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open RepresentationGrowth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (F : Type u) [Field F] [NumberField F]
  (G H : GroupScheme (Spec (CommRingCat.of F))) (f : G ⟶ H)

/-- A rational point factoring through the closed immersion on adelic points
already factors through it on rational points. -/
private theorem exists_rational_preimage
    [IsAffine G.X.left] [IsAffine H.X.left] [IsClosedImmersion f.hom.hom.left]
    (q : RationalGroupPoints F H) (p : normOneSubgroup F G)
    (hp : mapNormOne F G H f p = rationalNormOne F H q) :
    ∃ r : RationalGroupPoints F G, G.affinePointsTarget f (CommAlgCat.of F F) r = q := by
  let A := CommAlgCat.of F F
  let B := CommAlgCat.of F (Adeles F)
  let coeff : A ⟶ B := CommAlgCat.ofHom (Algebra.ofId F (Adeles F))
  let d := affineCoordinatePullback F f.hom.hom
  let z := (affineSchemePointEquiv F H.X F q).toAlgHom
  have hd : Function.Surjective d :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine f.hom.hom.left).2
  have hk : RingHom.ker d.toRingHom ≤ RingHom.ker z.toRingHom := by
    intro b hb
    change d b = 0 at hb
    change z b = 0
    apply NumberField.AdeleRing.algebraMap_injective (NumberField.RingOfIntegers F) F
    rw [map_zero]
    change coeff ((affineSchemePointEquiv F H.X F q) b) = 0
    rw [H.affineSchemePointEquiv_evaluation A, ← H.affinePointEvaluation_map coeff q]
    have hpoints : (p : AdelicGroupPoints F G) ≫ f.hom.hom = rational F H q :=
      congrArg Subtype.val hp
    calc
      H.affinePointEvaluation B (rational F H q) b =
          H.affinePointEvaluation B ((p : AdelicGroupPoints F G) ≫ f.hom.hom) b :=
        congrArg (fun x : AdelicGroupPoints F H => H.affinePointEvaluation B x b) hpoints.symm
      _ = G.affinePointEvaluation B p (d b) :=
        G.affinePointEvaluation_postcomp B f.hom.hom p b
      _ = 0 := by rw [hb, map_zero]
  let r := (affineSchemePointEquiv F G.X F).symm (AlgPoint.ofAlgHom (d.liftOfSurjective hd z hk))
  refine ⟨r, (affineSchemePointEquiv F H.X F).injective ?_⟩
  change affineSchemePointEquiv F H.X F (r ≫ f.hom.hom) = _
  rw [affineSchemePointEquiv_natural]
  dsimp only [r]
  rw [Equiv.apply_symm_apply]
  ext b
  exact AlgHom.liftOfSurjective_apply d hd z hk b

/-- Compact subsets of the ambient norm-one group meet only finitely many
rational translates of the source, indexed modulo its rational image. -/
private theorem exists_finite_rational_translates
    [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
    (hf : IsClosedSubgroup f) (K : Set (normOneSubgroup F H)) (hK : IsCompact K) :
    ∃ T : Set (RationalGroupPoints F H), T.Finite ∧
      ∀ (q : RationalGroupPoints F H) (p : normOneSubgroup F G),
        rationalNormOne F H q * mapNormOne F G H f p ∈ K →
          ∃ q' ∈ T, ∃ r : RationalGroupPoints F G,
            q = q' * G.affinePointsTarget f (CommAlgCat.of F F) r := by
  classical
  obtain ⟨d, j, ρ, hstab⟩ := Chevalley.exists_line_stabilizer F H G f hf
  let n := d + 1
  let e : Fin n → F := Pi.single j 1
  let eA : Fin n → Adeles F := Pi.single j 1
  let V := PrimitiveAdelicHeight.Vector F n
  let rat := PrimitiveAdelicHeight.rational F n
  let m := rationalMatrix F H ρ
  let M := adelicMatrix F H ρ
  let v (q : RationalGroupPoints F H) : Fin n → F := (m q).val *ᵥ e
  let w (y : normOneSubgroup F H) : V := (M (y : AdelicGroupPoints F H)).val *ᵥ eA
  have he : rat e = eA := by
    funext i
    by_cases hi : i = j <;> simp [rat, PrimitiveAdelicHeight.rational, e, eA, hi]
  have hwc : Continuous w := by
    apply continuous_pi
    intro i
    change Continuous (fun y : normOneSubgroup F H =>
      ((M (y : AdelicGroupPoints F H)).val *ᵥ Pi.single j 1) i)
    simp only [Matrix.mulVec_single_one, Matrix.col_apply]
    have hc : Continuous (fun a : Matrix (Fin n) (Fin n) (Adeles F) => a i j) :=
      (continuous_apply j).comp (continuous_apply i)
    exact hc.comp (Units.continuous_val.comp (M.continuous.comp continuous_subtype_val))
  have hline : (ρ.restrict f).PreservesCoordinateLine j := by
    intro X x
    simpa only [MatrixRepresentation.pointMatrix_restrict] using
      (hstab X (x ≫ f.hom.hom)).mp ⟨x, rfl⟩
  let χ : AlgebraicCharacter F G := (ρ.restrict f).coordinateLineCharacter j hline
  have hscale (p : normOneSubgroup F G) :
      (M (map F G H f p)).val *ᵥ eA = (character F G χ p).val • eA := by
    have h := (ρ.restrict f).affine_coordinateLineCharacter_action j hline
      (CommAlgCat.of F (Adeles F)) (p : AdelicGroupPoints F G)
    rw [MatrixRepresentation.affineMatrix_restrict] at h
    exact h
  have hprincipal (q : RationalGroupPoints F H) :
      (M (rational F H q)).val *ᵥ eA = rat (v q) := by
    change (adelicMatrix F H ρ (rational F H q)).val *ᵥ eA = _
    rw [adelicMatrix_rational, ← he, ← PrimitiveAdelicHeight.rational_mulVec]
  have hw (q : RationalGroupPoints F H) (p : normOneSubgroup F G) :
      w (rationalNormOne F H q * mapNormOne F G H f p) =
        (character F G χ p).val • rat (v q) := by
    change (M (rational F H q * map F G H f p)).val *ᵥ eA = _
    rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hscale p, Matrix.mulVec_smul,
      hprincipal q]
  have hsame (q q' : RationalGroupPoints F H) (a b : Fˣ)
      (hab : (a : F) • v q = (b : F) • v q') :
      ∃ r : RationalGroupPoints F G, q = q' * G.affinePointsTarget f (CommAlgCat.of F F) r := by
    have hv : v q = ((a⁻¹ * b : Fˣ) : F) • v q' := by
      change a • v q = b • v q' at hab
      change v q = (a⁻¹ * b) • v q'
      rw [mul_smul, ← hab, inv_smul_smul]
    have hs : (m (q'⁻¹ * q)).val *ᵥ e = ((a⁻¹ * b : Fˣ) : F) • e := by
      rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec]
      change (m q'⁻¹).val *ᵥ v q = _
      rw [hv, Matrix.mulVec_smul]
      change ((a⁻¹ * b : Fˣ) : F) • ((m q'⁻¹).val *ᵥ ((m q').val *ᵥ e)) = _
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one,
        Units.val_one, Matrix.one_mulVec]
    have hs' := (ρ.affine_coordinateLine_scalar_iff (CommAlgCat.of F F) (q'⁻¹ * q) j).mpr
      ⟨a⁻¹ * b, hs⟩
    obtain ⟨r, hr⟩ := (hstab _ (q'⁻¹ * q)).mpr hs'
    change G.affinePointsTarget f (CommAlgCat.of F F) r = q'⁻¹ * q at hr
    exact ⟨r, by rw [hr, mul_inv_cancel_left]⟩
  obtain ⟨C, hC, _, hcover⟩ := NormOneIdeleClass.exists_isCompact_fundamentalSet F
  let B : Set V := (fun xy : Ideles F × V => xy.1 • xy.2) '' (C ×ˢ (w '' K))
  have hB : IsCompact B := (hC.prod (hK.image hwc)).image (continuous_fst.smul continuous_snd)
  let S : Set (Fin n → F) := {x | rat x ∈ B ∧
    ∃ (q : RationalGroupPoints F H) (a : Fˣ), (a : F) • v q = x}
  have hS : S.Finite := by
    apply ((PrimitiveAdelicHeight.finite_inter_rational_range F n B hB).preimage
      (PrimitiveAdelicHeight.rational_injective F n).injOn).subset
    exact fun x hx => ⟨hx.1, Set.mem_range_self x⟩
  have : Finite S := hS
  let repr (x : S) : RationalGroupPoints F H := x.property.2.choose
  refine ⟨Set.range repr, Set.finite_range repr, fun q p hp => ?_⟩
  let t := character F G χ p
  have ht : t ∈ NormOneIdeleClass.normOneIdeles F :=
    (mem_normOneSubgroup F G p).mp p.property χ
  obtain ⟨a, ha⟩ := hcover t⁻¹ ((NormOneIdeleClass.normOneIdeles F).inv_mem ht)
  have hmem : rat ((a : F) • v q) ∈ B := by
    refine ⟨(diagonalUnits F a * t⁻¹, w _), ⟨ha, ⟨_, hp, rfl⟩⟩, ?_⟩
    change (diagonalUnits F a * t⁻¹) • w (rationalNormOne F H q * mapNormOne F G H f p) = _
    rw [hw]
    change (diagonalUnits F a * t⁻¹) • (t • rat (v q)) = _
    rw [smul_smul, inv_mul_cancel_right]
    exact (PrimitiveAdelicHeight.rational_smul F n a (v q)).symm
  let x : S := ⟨(a : F) • v q, hmem, q, a, rfl⟩
  obtain ⟨b, hb⟩ := x.property.2.choose_spec
  exact ⟨repr x, Set.mem_range_self x, hsame q (repr x) a b hb.symm⟩

/-- Springer's closed subgroup lemma for the actual norm-one adelic quotients. -/
theorem normOneRationalQuotientClosedImmersion :
    NormOneRationalQuotientClosedImmersionStatement.{u} := by
  intro F _ _ G H _ _ _ _ f hf
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  have : IsClosedImmersion f.hom.hom.left := hf
  let m := mapNormOne F G H f
  let rG := rationalNormOne F G
  let rH := rationalNormOne F H
  let ΓG := rationalNormOneSubgroup F G
  let ΓH := rationalNormOneSubgroup F H
  have hm : IsClosedEmbedding m := by
    apply IsClosedEmbedding.of_comp (IsEmbedding.subtypeVal (p := (· ∈ normOneSubgroup F H)))
    exact (isClosedEmbedding_map F G H f).comp
      (isClosed_normOneSubgroup F G).isClosedEmbedding_subtypeVal
  apply IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_normOneRationalQuotientMap F G H f)
  · intro x y hxy
    revert hxy
    refine Quotient.inductionOn₂ x y ?_
    intro p p' h
    change LeftCosetSpace.mk ΓH (m p) = LeftCosetSpace.mk ΓH (m p') at h
    obtain ⟨q, hq⟩ := (LeftCosetSpace.mk_eq_mk_iff ΓH _ _).mp h
    change rH q = m p' * (m p)⁻¹ at hq
    have hmp : m (p' * p⁻¹) = rH q := by rw [map_mul, map_inv, hq]
    obtain ⟨r, hr⟩ := exists_rational_preimage F G H f q _ hmp
    apply (LeftCosetSpace.mk_eq_mk_iff ΓG p p').mpr
    refine ⟨r, hm.injective ?_⟩
    change mapNormOne F G H f (rG r) = m (p' * p⁻¹)
    rw [mapNormOne_rationalNormOne, hr, hmp]
  · intro D hD
    let E := LeftCosetSpace.mk ΓG ⁻¹' D
    let J (q : RationalGroupPoints F H) := (fun p => rH q * m p) '' E
    let S := ⋃ q, J q
    have hE : IsClosed E := hD.preimage (LeftCosetSpace.continuous_mk ΓG)
    have hJ (q : RationalGroupPoints F H) : IsClosed (J q) :=
      ((Homeomorph.mulLeft (rH q)).isClosedEmbedding.comp hm).isClosedMap E hE
    apply (LeftCosetSpace.isQuotientMap_mk ΓH).isCoinducing.isClosed_preimage.mp
    have hpre : LeftCosetSpace.mk ΓH ⁻¹' (normOneRationalQuotientMap F G H f '' D) = S := by
      ext y
      constructor
      · rintro ⟨c, hc, heq⟩
        obtain ⟨p, rfl⟩ := LeftCosetSpace.mk_surjective ΓG c
        change LeftCosetSpace.mk ΓH (m p) = LeftCosetSpace.mk ΓH y at heq
        obtain ⟨q, hq⟩ := (LeftCosetSpace.mk_eq_mk_iff ΓH _ _).mp heq
        change rH q = y * (m p)⁻¹ at hq
        refine Set.mem_iUnion.mpr ⟨q, p, hc, ?_⟩
        change rH q * m p = y
        rw [hq, inv_mul_cancel_right]
      · intro hy
        obtain ⟨q, p, hp, rfl⟩ := Set.mem_iUnion.mp hy
        exact ⟨LeftCosetSpace.mk ΓG p, hp,
          (LeftCosetSpace.mk_subgroup_mul ΓH ⟨rH q, q, rfl⟩ (m p)).symm⟩
    rw [hpre]
    apply isClosed_of_closure_subset
    intro y hy
    obtain ⟨K, hK, hKy⟩ := exists_compact_mem_nhds y
    obtain ⟨T, hT, hfinite⟩ := exists_finite_rational_translates F G H f hf K hK
    let U := ⋃ q ∈ T, J q
    have hU : IsClosed U := hT.isClosed_biUnion fun q _ => hJ q
    have hcover : S ∩ K ⊆ U := by
      rintro z ⟨hz, hzK⟩
      obtain ⟨q, p, hp, rfl⟩ := Set.mem_iUnion.mp hz
      obtain ⟨q', hq', r, hr⟩ := hfinite q p hzK
      have hrew : rH q * m p = rH q' * m (rG r * p) := by
        rw [hr, map_mul, map_mul, mapNormOne_rationalNormOne, mul_assoc]
      refine Set.mem_iUnion₂.mpr ⟨q', hq', rG r * p, ?_, hrew.symm⟩
      change LeftCosetSpace.mk ΓG (rG r * p) ∈ D
      rwa [LeftCosetSpace.mk_subgroup_mul ΓG ⟨rG r, r, rfl⟩ p]
    have hyU : y ∈ closure U := by
      apply mem_closure_iff_nhds'.mpr
      intro W hW
      obtain ⟨z, hz⟩ := mem_closure_iff_nhds'.mp hy (W ∩ K) (Filter.inter_mem hW hKy)
      exact ⟨⟨z, hcover ⟨z.property, hz.2⟩⟩, hz.1⟩
    rw [hU.closure_eq] at hyU
    obtain ⟨q, _, hq⟩ := Set.mem_iUnion₂.mp hyU
    exact Set.mem_iUnion.mpr ⟨q, hq⟩

end Langlands.Global.AdelicGroupPoints
