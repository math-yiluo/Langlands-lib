import Langlands.AlgebraicGeometry.Picard.StalkDerivationTangent
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Smooth.Local
import Mathlib.RingTheory.Kaehler.JacobiZariski
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.RingHom.EssFiniteType
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Smoothness and dense range from surjectivity on rational tangent vectors -/

universe u

open TensorProduct KaehlerDifferential

noncomputable section

namespace Langlands.AlgebraicGeometry.TangentSmoothness

section SplitCriterion

variable {B M N K : Type*} [CommRing B] [IsLocalRing B] [AddCommGroup M] [Module B M]
  [AddCommGroup N] [Module B N] [Field K] [Algebra B K]

/-- Over a local ring `B` with residue field `K`, a linear map `l : M → N` from a finite module
to a finite free module is split injective when every linear form `M → K` extends along `l`. -/
theorem exists_leftInverse_of_forall_extend [Module.Finite B M] [Module.Finite B N]
    [Module.Free B N] (hK : Function.Surjective (algebraMap B K)) (l : M →ₗ[B] N)
    (h : ∀ g₀ : M →ₗ[B] K, ∃ μ : N →ₗ[B] K, μ ∘ₗ l = g₀) :
    ∃ l' : N →ₗ[B] M, l' ∘ₗ l = LinearMap.id := by
  rw [IsLocalRing.split_injective_iff_lTensor_residueField_injective]
  have hker : RingHom.ker (algebraMap B K) = IsLocalRing.maximalIdeal B :=
    ((RingHom.ker_isMaximal_of_surjective _ hK).eq_of_le (IsLocalRing.maximalIdeal.isMaximal B).ne_top
      (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)))
  let e₀ : IsLocalRing.ResidueField B ≃ₐ[B] K :=
    AlgEquiv.ofRingEquiv (f := (Ideal.quotEquivOfEq hker.symm).trans
      (RingHom.quotientKerEquivOfSurjective hK)) (fun _ => rfl)
  let e : IsLocalRing.ResidueField B ≃ₗ[B] K := e₀.toLinearEquiv
  rw [← LinearMap.baseChange_eq_ltensor, ← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  rw [← Module.forall_dual_apply_eq_zero_iff (IsLocalRing.ResidueField B) v]
  intro φ
  obtain ⟨μ, hμ⟩ := h (e.toLinearMap ∘ₗ (φ.restrictScalars B) ∘ₗ
    TensorProduct.mk B (IsLocalRing.ResidueField B) M 1)
  let μ' : IsLocalRing.ResidueField B ⊗[B] N →ₗ[IsLocalRing.ResidueField B]
      IsLocalRing.ResidueField B :=
    LinearMap.liftBaseChange _ (e.symm.toLinearMap ∘ₗ μ)
  have hφ : μ' ∘ₗ l.baseChange (IsLocalRing.ResidueField B) = φ := by
    ext m
    have := congr(e.symm ($hμ m))
    simpa [μ'] using this
  rw [← hφ, LinearMap.comp_apply, hv, map_zero]

end SplitCriterion

section JacobiZariski

variable {k A B : Type*} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  [Algebra A B] [IsScalarTower k A B]

/-- If `B` is formally smooth over `k` and the first map `B ⊗[A] Ω[A⁄k] → Ω[B⁄k]` of the
Jacobi–Zariski sequence has a left inverse, then `B` is formally smooth over `A`. -/
theorem formallySmooth_of_mapBaseChange_split [Algebra.FormallySmooth k B]
    (l : Ω[B⁄k] →ₗ[B] B ⊗[A] Ω[A⁄k]) (hl : l ∘ₗ mapBaseChange k A B = LinearMap.id) :
    Algebra.FormallySmooth A B := by
  have hinj : Function.Injective (mapBaseChange k A B) := fun x y hxy => by
    have := congr(l $hxy)
    rwa [← LinearMap.comp_apply, ← LinearMap.comp_apply, hl, LinearMap.id_apply,
      LinearMap.id_apply] at this
  obtain ⟨-, s, hs⟩ := ((exact_mapBaseChange_map k A B).split_tfae'.out 2 1 rfl rfl).mp
    ⟨map_surjective k A B, l, hl⟩
  refine ⟨Module.Projective.of_split s (map k A B B) hs, ⟨fun x y => ?_⟩⟩
  have hδ : Function.Injective (Algebra.H1Cotangent.δ k A B) := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨w, rfl⟩ := (Algebra.H1Cotangent.exact_map_δ k A B z).mp hz
    rw [Subsingleton.elim w 0, map_zero]
  have hzero : ∀ z, Algebra.H1Cotangent.δ k A B z = 0 := fun z =>
    hinj (by rw [(Algebra.H1Cotangent.exact_δ_mapBaseChange k A B).apply_apply_eq_zero, map_zero])
  exact hδ (by rw [hzero, hzero])

end JacobiZariski

section Derivations

variable {k A B K : Type*} [CommRing k] [CommRing A] [CommRing B] [IsLocalRing B] [Field K]
  [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
  [Algebra k K] [Algebra A K] [Algebra B K] [IsScalarTower k A K] [IsScalarTower k B K]
  [IsScalarTower A B K]

/-- **Smoothness from extension of derivations.** Let `k → A → B` be ring maps with `B` local
and formally smooth over `k`, `Ω[A⁄k]` and `Ω[B⁄k]` finite, and let `B → K` be a surjection
onto a field. If every `k`-derivation `A → K` extends to a `k`-derivation `B → K`, then `B` is
formally smooth over `A`. -/
theorem formallySmooth_of_forall_derivation_extend [Algebra.FormallySmooth k B]
    [Module.Finite A Ω[A⁄k]] [Module.Finite B Ω[B⁄k]]
    (hK : Function.Surjective (algebraMap B K))
    (h : ∀ D : Derivation k A K, ∃ D' : Derivation k B K, D'.compAlgebraMap A = D) :
    Algebra.FormallySmooth A B := by
  have : Module.Free B Ω[B⁄k] := Module.free_of_flat_of_isLocalRing
  obtain ⟨l, hl⟩ := exists_leftInverse_of_forall_extend hK (mapBaseChange k A B) fun g₀ => by
    obtain ⟨D', hD'⟩ := h ((g₀.restrictScalars A ∘ₗ TensorProduct.mk A B Ω[A⁄k] 1).compDer
      (KaehlerDifferential.D k A))
    refine ⟨D'.liftKaehlerDifferential, ?_⟩
    ext a
    have := congr($hD' a)
    simpa using this
  exact formallySmooth_of_mapBaseChange_split l hl

end Derivations

section Scheme

open CategoryTheory _root_.AlgebraicGeometry _root_.Langlands.AlgebraicGeometry.Picard

variable {K : Type u} [Field K] {X Y : Scheme.{u}}

/-- A morphism `f : X ⟶ Y` of schemes over `Spec K` is surjective on rational tangent vectors
at a `K`-point `x` of `X` when every `K[ε]`-point of `Y` over `K` restricting to `x ≫ f` is the
image under `f` of a `K[ε]`-point of `X` over `K` restricting to `x`. -/
def IsTangentSurjectiveAt (p : X ⟶ Spec (CommRingCat.of K)) (q : Y ⟶ Spec (CommRingCat.of K))
    (f : X ⟶ Y) (x : Spec (CommRingCat.of K) ⟶ X) : Prop :=
  ∀ t, IsTangentVectorAt q (x ≫ f) t → ∃ s, IsTangentVectorAt p x s ∧ s ≫ f = t

lemma formallySmooth_toStalk (P : PrimeSpectrum K) :
    (StructureSheaf.toStalk K P).hom.FormallySmooth :=
  Algebra.FormallySmooth.of_isLocalization (Rₘ := (structurePresheafInCommRingCat K).stalk P)
    P.asIdeal.primeCompl

lemma essFiniteType_toStalk (P : PrimeSpectrum K) :
    (StructureSheaf.toStalk K P).hom.EssFiniteType :=
  Algebra.EssFiniteType.of_isLocalization ((structurePresheafInCommRingCat K).stalk P)
    P.asIdeal.primeCompl

/-- The structure map of a stalk over `K` factors through the stalk of `Spec K`. -/
lemma stalkAlgebraOver_algebraMap (p : X ⟶ Spec (CommRingCat.of K)) (z : X) :
    letI := stalkAlgebraOver p z
    algebraMap K (X.presheaf.stalk z) =
      (p.stalkMap z).hom.comp (StructureSheaf.toStalk K (p z)).hom := by
  let := stalkAlgebraOver p z
  change (Spec.preimage (X.fromSpecStalk z ≫ p)).hom = _
  have h : Spec.map (StructureSheaf.toStalk _ (p z) ≫ p.stalkMap z) = X.fromSpecStalk z ≫ p :=
    (Spec.map_comp _ _).trans ((congrArg (Spec.map (p.stalkMap z) ≫ ·)
      (Spec.fromSpecStalk_eq' _ (p z)).symm).trans (Scheme.SpecMap_stalkMap_fromSpecStalk p))
  rw [← h, Spec.preimage_map]
  rfl

lemma formallySmooth_stalkAlgebraOver (p : X ⟶ Spec (CommRingCat.of K)) [Smooth p] (z : X) :
    letI := stalkAlgebraOver p z
    Algebra.FormallySmooth K (X.presheaf.stalk z) := by
  let := stalkAlgebraOver p z
  have h₂ : (p.stalkMap z).hom.FormallySmooth := by
    rw [← Scheme.Hom.mem_smoothLocus, p.smoothLocus_eq_top]
    trivial
  rw [← RingHom.formallySmooth_algebraMap, stalkAlgebraOver_algebraMap]
  exact (formallySmooth_toStalk (p z)).comp h₂

lemma essFiniteType_stalkAlgebraOver (p : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType p]
    (z : X) :
    letI := stalkAlgebraOver p z
    Algebra.EssFiniteType K (X.presheaf.stalk z) := by
  let := stalkAlgebraOver p z
  rw [← RingHom.essFiniteType_algebraMap, stalkAlgebraOver_algebraMap]
  exact (essFiniteType_toStalk (p z)).comp (LocallyOfFiniteType.stalkMap p z)

/-- Stalk maps of a morphism over `Spec K` are `K`-algebra maps. -/
lemma stalkMap_comp_stalkAlgebraOver_algebraMap {p : X ⟶ Spec (CommRingCat.of K)}
    {q : Y ⟶ Spec (CommRingCat.of K)} (f : X ⟶ Y) (hf : f ≫ q = p) (z : X) :
    (f.stalkMap z).hom.comp (@algebraMap K _ _ _ (stalkAlgebraOver q (f z))) =
      @algebraMap K _ _ _ (stalkAlgebraOver p z) := by
  change (f.stalkMap z).hom.comp (Spec.preimage (Y.fromSpecStalk (f z) ≫ q)).hom =
    (Spec.preimage (X.fromSpecStalk z ≫ p)).hom
  rw [← CommRingCat.hom_comp]
  congr 1
  apply Spec.map_injective
  rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, ← Category.assoc,
    Scheme.SpecMap_stalkMap_fromSpecStalk, Category.assoc, hf]

/-- The rational augmentation at `x ≫ f` is the stalk map of `f` followed by the rational
augmentation at `x`. -/
lemma rationalStalkAugmentation_comp_stalkMap {p : X ⟶ Spec (CommRingCat.of K)}
    {q : Y ⟶ Spec (CommRingCat.of K)} (f : X ⟶ Y) {x : Spec (CommRingCat.of K) ⟶ X}
    (hx : IsRationalPoint p x) (hx' : IsRationalPoint q (x ≫ f)) :
    letI := stalkAlgebraOver q ((x ≫ f) (IsLocalRing.closedPoint K))
    letI := stalkAlgebraOver p (x (IsLocalRing.closedPoint K))
    (rationalStalkAugmentation q (x ≫ f) hx').toRingHom =
      (rationalStalkAugmentation p x hx).toRingHom.comp
        (f.stalkMap (x (IsLocalRing.closedPoint K))).hom := by
  let := stalkAlgebraOver q ((x ≫ f) (IsLocalRing.closedPoint K))
  let := stalkAlgebraOver p (x (IsLocalRing.closedPoint K))
  rw [rationalStalkAugmentation_toRingHom, rationalStalkAugmentation_toRingHom,
    Scheme.stalkClosedPointTo_comp]
  rfl

/-- A morphism `f` between schemes locally of finite type over `Spec K` is locally of finite
presentation. -/
lemma locallyOfFinitePresentation_of_comp_eq {p : X ⟶ Spec (CommRingCat.of K)}
    {q : Y ⟶ Spec (CommRingCat.of K)} (f : X ⟶ Y) (hf : f ≫ q = p) [LocallyOfFiniteType p]
    [LocallyOfFiniteType q] : LocallyOfFinitePresentation f := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian q
  have : LocallyOfFiniteType (f ≫ q) := hf ▸ inferInstance
  have := locallyOfFiniteType_of_comp f q
  infer_instance

/-- **Smoothness from surjectivity on rational tangent vectors.** Let `f : X ⟶ Y` be a morphism
over `Spec K` with `X` smooth and `Y` locally of finite type over `K`, and let `x` be a
`K`-point of `X`. If `f` is surjective on rational tangent vectors at `x`, then the stalk map of
`f` at `x` is formally smooth. -/
theorem formallySmooth_stalkMap_of_isTangentSurjectiveAt {p : X ⟶ Spec (CommRingCat.of K)}
    {q : Y ⟶ Spec (CommRingCat.of K)} [Smooth p] [LocallyOfFiniteType q] (f : X ⟶ Y)
    (hf : f ≫ q = p) {x : Spec (CommRingCat.of K) ⟶ X} (hx : IsRationalPoint p x)
    (h : IsTangentSurjectiveAt p q f x) :
    (f.stalkMap (x (IsLocalRing.closedPoint K))).hom.FormallySmooth := by
  have hx' : IsRationalPoint q (x ≫ f) := by
    rw [IsRationalPoint, Category.assoc, hf]
    exact hx
  let _ : Algebra K (Y.presheaf.stalk ((x ≫ f) (IsLocalRing.closedPoint K))) :=
    stalkAlgebraOver q ((x ≫ f) (IsLocalRing.closedPoint K))
  let _ : Algebra K (X.presheaf.stalk (x (IsLocalRing.closedPoint K))) :=
    stalkAlgebraOver p (x (IsLocalRing.closedPoint K))
  let _ : Algebra (Y.presheaf.stalk ((x ≫ f) (IsLocalRing.closedPoint K)))
      (X.presheaf.stalk (x (IsLocalRing.closedPoint K))) :=
    (f.stalkMap (x (IsLocalRing.closedPoint K))).hom.toAlgebra
  let _ : Algebra (Y.presheaf.stalk ((x ≫ f) (IsLocalRing.closedPoint K))) K :=
    (rationalStalkAugmentation q (x ≫ f) hx').toRingHom.toAlgebra
  let _ : Algebra (X.presheaf.stalk (x (IsLocalRing.closedPoint K))) K :=
    (rationalStalkAugmentation p x hx).toRingHom.toAlgebra
  change Algebra.FormallySmooth (Y.presheaf.stalk ((x ≫ f) (IsLocalRing.closedPoint K)))
    (X.presheaf.stalk (x (IsLocalRing.closedPoint K)))
  have : IsScalarTower K (Y.presheaf.stalk ((x ≫ f) (IsLocalRing.closedPoint K)))
      (X.presheaf.stalk (x (IsLocalRing.closedPoint K))) :=
    .of_algebraMap_eq' (stalkMap_comp_stalkAlgebraOver_algebraMap f hf _).symm
  have : IsScalarTower K (Y.presheaf.stalk ((x ≫ f) (IsLocalRing.closedPoint K))) K :=
    .of_algebraMap_eq' (RingHom.ext fun c => ((rationalStalkAugmentation q (x ≫ f) hx').commutes c).symm)
  have : IsScalarTower K (X.presheaf.stalk (x (IsLocalRing.closedPoint K))) K :=
    .of_algebraMap_eq' (RingHom.ext fun c => ((rationalStalkAugmentation p x hx).commutes c).symm)
  have : IsScalarTower (Y.presheaf.stalk ((x ≫ f) (IsLocalRing.closedPoint K)))
      (X.presheaf.stalk (x (IsLocalRing.closedPoint K))) K :=
    .of_algebraMap_eq' (rationalStalkAugmentation_comp_stalkMap f hx hx')
  have := formallySmooth_stalkAlgebraOver p (x (IsLocalRing.closedPoint K))
  have := essFiniteType_stalkAlgebraOver p (x (IsLocalRing.closedPoint K))
  have := essFiniteType_stalkAlgebraOver q ((x ≫ f) (IsLocalRing.closedPoint K))
  have hK : Function.Surjective
      (algebraMap (X.presheaf.stalk (x (IsLocalRing.closedPoint K))) K) := fun c =>
    ⟨algebraMap K _ c, (rationalStalkAugmentation p x hx).commutes c⟩
  refine formallySmooth_of_forall_derivation_extend (k := K) hK fun D => ?_
  obtain ⟨s, hs, hsf⟩ := h _ (rationalStalkDerivationTangentEquiv q (x ≫ f) hx' D).2
  obtain ⟨D', hD'⟩ := (rationalStalkDerivationTangentEquiv p x hx).surjective ⟨s, hs⟩
  refine ⟨D', (rationalStalkDerivationTangentEquiv q (x ≫ f) hx').injective (Subtype.ext ?_)⟩
  rw [← hsf, ← show (rationalStalkDerivationTangentEquiv p x hx D').val = s from
      congrArg Subtype.val hD', rationalStalkDerivationTangentEquiv_apply_val,
    rationalStalkDerivationTangentEquiv_apply_val, Category.assoc,
    ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Spec.map_comp_assoc]
  congr 2
  ext a
  · exact congr($(rationalStalkAugmentation_comp_stalkMap f hx hx') a)
  · rfl

/-- Under the hypotheses of `formallySmooth_stalkMap_of_isTangentSurjectiveAt`, the point `x`
lies in the smooth locus of `f`. -/
theorem mem_smoothLocus_of_isTangentSurjectiveAt {p : X ⟶ Spec (CommRingCat.of K)}
    {q : Y ⟶ Spec (CommRingCat.of K)} [Smooth p] [LocallyOfFiniteType q] (f : X ⟶ Y)
    (hf : f ≫ q = p) [LocallyOfFinitePresentation f] {x : Spec (CommRingCat.of K) ⟶ X}
    (hx : IsRationalPoint p x) (h : IsTangentSurjectiveAt p q f x) :
    x (IsLocalRing.closedPoint K) ∈ f.smoothLocus :=
  formallySmooth_stalkMap_of_isTangentSurjectiveAt f hf hx h

/-- **Dense range from surjectivity on rational tangent vectors.** Let `f : X ⟶ Y` be a
morphism over `Spec K` with `X` smooth over `K` and `Y` irreducible and locally of finite type
over `K`. If `f` is surjective on rational tangent vectors at some `K`-point of `X`, then `f`
has dense range. -/
theorem denseRange_of_isTangentSurjectiveAt {p : X ⟶ Spec (CommRingCat.of K)}
    {q : Y ⟶ Spec (CommRingCat.of K)} [Smooth p] [LocallyOfFiniteType q] [IrreducibleSpace Y]
    (f : X ⟶ Y) (hf : f ≫ q = p) {x : Spec (CommRingCat.of K) ⟶ X}
    (hx : IsRationalPoint p x) (h : IsTangentSurjectiveAt p q f x) : DenseRange f := by
  have := locallyOfFinitePresentation_of_comp_eq f hf
  have hz := mem_smoothLocus_of_isTangentSurjectiveAt f hf hx h
  have : Smooth (f.smoothLocus.ι ≫ f) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq,
      Scheme.Opens.ι_preimage_self]
  have hopen : IsOpen (Set.range (f.smoothLocus.ι ≫ f)) :=
    (f.smoothLocus.ι ≫ f).isOpenMap.isOpen_range
  refine (hopen.dense ⟨_, ⟨⟨_, hz⟩, rfl⟩⟩).mono ?_
  rintro _ ⟨u, rfl⟩
  exact ⟨f.smoothLocus.ι u, rfl⟩

end Scheme

end Langlands.AlgebraicGeometry.TangentSmoothness
