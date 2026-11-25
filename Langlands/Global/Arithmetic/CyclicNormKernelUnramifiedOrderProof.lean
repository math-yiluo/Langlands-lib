import Langlands.Automorphic.WeakInductionAssociationReduction
import Langlands.ClassFieldTheory.Global.FundamentalClassProof
import Langlands.ClassFieldTheory.Global.IdeleClassNormGaloisProductProof
import Langlands.ClassFieldTheory.Global.LocalRelativeWeilMapExistenceProof
import Langlands.ClassFieldTheory.Global.RelativeWeilTransferReciprocityProof
import Langlands.ClassFieldTheory.Global.RelativeWeilUnramifiedTwist
import Langlands.ClassFieldTheory.Local.LocalRelativeClassFormationProof
import Langlands.ClassFieldTheory.Local.WeilReciprocityExistenceProof
import Langlands.Global.Arithmetic.CyclicNormKernelUnramifiedOrderStatement
import Mathlib.FieldTheory.PrimitiveElement

/-! # The local order of a cyclic norm-kernel character -/

noncomputable section

open scoped NumberField

universe u v w uF uE

set_option autoImplicit false

namespace Langlands.Global.HeckeCharacter

open NumberField IsDedekindDomain
open Langlands.ClassFieldTheory.Global Langlands.ClassFieldTheory.Local
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic

/-! ### Transport along an isomorphism of the extension field -/

section Transport

variable {F : Type u} {E : Type v} {E' : Type w} [Field F] [NumberField F]
  [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra F E] [Algebra F E']
  (φ : E ≃ₐ[F] E')

omit [NumberField F] [NumberField E] [NumberField E'] in
/-- The place of `E` pulled back from a place of `E'` lies over the same place of `F`. -/
theorem finitePlaceEquiv_algEquiv_under (q : HeightOneSpectrum (𝓞 E')) :
    (finitePlaceEquiv φ.toRingEquiv q).under (𝓞 F) = q.under (𝓞 F) := by
  apply HeightOneSpectrum.ext
  ext x
  change RingOfIntegers.mapRingEquiv φ.toRingEquiv (algebraMap (𝓞 F) (𝓞 E) x) ∈ q.asIdeal ↔
    algebraMap (𝓞 F) (𝓞 E') x ∈ q.asIdeal
  have hx : RingOfIntegers.mapRingEquiv φ.toRingEquiv (algebraMap (𝓞 F) (𝓞 E) x) =
      algebraMap (𝓞 F) (𝓞 E') x := RingOfIntegers.ext (φ.commutes (x : F))
  rw [hx]

omit [NumberField F] [NumberField E] in
theorem liesOver_finitePlaceEquiv_algEquiv (p : HeightOneSpectrum (𝓞 F))
    (q : HeightOneSpectrum (𝓞 E')) [q.asIdeal.LiesOver p.asIdeal] :
    (finitePlaceEquiv φ.toRingEquiv q).asIdeal.LiesOver p.asIdeal := by
  have h := liesOver_under (K := F) (finitePlaceEquiv φ.toRingEquiv q)
  rwa [finitePlaceEquiv_algEquiv_under, finitePlacesAbove_under p ⟨q, inferInstance⟩] at h

/-- The completed transport along `φ` is compatible with the completed embeddings of `F_p`. -/
theorem finiteCompletionEquiv_algEquiv_completionMap (p : HeightOneSpectrum (𝓞 F))
    (q : HeightOneSpectrum (𝓞 E')) [q.asIdeal.LiesOver p.asIdeal]
    [(finitePlaceEquiv φ.toRingEquiv q).asIdeal.LiesOver p.asIdeal] (x : p.adicCompletion F) :
    finiteCompletionEquiv φ.toRingEquiv q
        (FiniteExtension.completionMap p (finitePlaceEquiv φ.toRingEquiv q) x) =
      FiniteExtension.completionMap p q x := by
  refine congrFun ((p.denseRange_algebraMap F).equalizer
    ((continuous_finiteCompletionEquiv φ.toRingEquiv q).comp
      (FiniteExtension.continuous_completionMap p _))
    (FiniteExtension.continuous_completionMap p q) ?_) x
  funext a
  simp only [Function.comp_apply, FiniteExtension.completionMap_coe, finiteCompletionEquiv_coe]
  exact congrArg _ (φ.commutes a)

theorem finiteAdeleEquiv_algEquiv_finiteAdeleInclusion (x : FiniteAdeleRing (𝓞 F) F) :
    finiteAdeleEquiv φ.toRingEquiv (finiteAdeleInclusion (L := E) x) =
      finiteAdeleInclusion (L := E') x := by
  apply FiniteAdeleRing.ext
  intro q
  have := liesOver_finitePlaceEquiv_algEquiv φ (q.under (𝓞 F)) q
  rw [finiteAdeleEquiv_apply,
    IdeleGaloisDescentProof.finiteAdeleInclusion_apply_of_liesOver x (q.under (𝓞 F))
      (finitePlaceEquiv φ.toRingEquiv q),
    finiteCompletionEquiv_algEquiv_completionMap, finiteAdeleInclusion_apply]

theorem infiniteAdeleEquiv_algEquiv_infiniteAdeleMap (x : InfiniteAdeleRing F) :
    infiniteAdeleEquiv φ.toRingEquiv (infiniteAdeleMap (algebraMap F E) x) =
      infiniteAdeleMap (algebraMap F E') x := by
  have hc : φ.toRingEquiv.toRingHom.comp (algebraMap F E) = algebraMap F E' := by
    ext a
    exact φ.commutes a
  change infiniteAdeleMap φ.toRingEquiv.toRingHom (infiniteAdeleMap (algebraMap F E) x) = _
  rw [← RingHom.comp_apply, ← infiniteAdeleMap_comp, hc]

theorem adeleEquiv_algEquiv_adeleInclusion (x : AdeleRing (𝓞 F) F) :
    adeleEquiv φ.toRingEquiv (adeleInclusion (L := E) x) = adeleInclusion (L := E') x :=
  Prod.ext (infiniteAdeleEquiv_algEquiv_infiniteAdeleMap φ x.1)
    (finiteAdeleEquiv_algEquiv_finiteAdeleInclusion φ x.2)

/-- The idele-class transport along `φ` carries the inclusion of `C_F` into `C_E` to the
inclusion of `C_F` into `C_{E'}`. -/
theorem ideleClassEquiv_algEquiv_ideleClassInclusion (x : IdeleClassGroup (𝓞 F) F) :
    ideleClassEquiv φ.toRingEquiv (ideleClassInclusion (K := F) (L := E) x) =
      ideleClassInclusion (K := F) (L := E') x := by
  refine QuotientGroup.induction_on x fun a => ?_
  change QuotientGroup.mk (ideleEquiv φ.toRingEquiv (ideleInclusion a)) =
    QuotientGroup.mk (ideleInclusion a)
  congr 1
  apply Units.ext
  exact adeleEquiv_algEquiv_adeleInclusion φ (a : AdeleRing (𝓞 F) F)

omit [NumberField F] in
theorem ideleClassEquiv_symm_apply_apply (y : IdeleClassGroup (𝓞 E) E) :
    ideleClassEquiv φ.symm.toRingEquiv (ideleClassEquiv φ.toRingEquiv y) = y := by
  have h : φ.toRingEquiv.trans φ.symm.toRingEquiv = RingEquiv.refl E := by
    ext x
    exact φ.symm_apply_apply x
  have h1 := ideleClassEquiv_trans φ.toRingEquiv φ.symm.toRingEquiv
  rw [h, ideleClassEquiv_refl] at h1
  exact (DFunLike.congr_fun h1 y).symm

omit [NumberField F] in
/-- Conjugating a relative automorphism by `φ` conjugates its idele-class action. -/
theorem relativeIdeleClassAut_autCongr (σ : E ≃ₐ[F] E) (y : IdeleClassGroup (𝓞 E) E) :
    relativeIdeleClassAut F E' (AlgEquiv.autCongr φ σ) (ideleClassEquiv φ.toRingEquiv y) =
      ideleClassEquiv φ.toRingEquiv (relativeIdeleClassAut F E σ y) := by
  have hσ : (AlgEquiv.autCongr φ σ).toRingEquiv =
      φ.symm.toRingEquiv.trans (σ.toRingEquiv.trans φ.toRingEquiv) := RingEquiv.ext fun _ => rfl
  change ideleClassEquiv (AlgEquiv.autCongr φ σ).toRingEquiv (ideleClassEquiv φ.toRingEquiv y) =
    ideleClassEquiv φ.toRingEquiv (ideleClassEquiv σ.toRingEquiv y)
  rw [hσ, ideleClassEquiv_trans, ideleClassEquiv_trans]
  change ideleClassEquiv φ.toRingEquiv (ideleClassEquiv σ.toRingEquiv
    (ideleClassEquiv φ.symm.toRingEquiv (ideleClassEquiv φ.toRingEquiv y))) = _
  rw [ideleClassEquiv_symm_apply_apply]

variable [IsGalois F E] [IsGalois F E']

/-- The idele-class norm is unchanged on transporting the extension field along `φ`. -/
theorem ideleClassNorm_ideleClassEquiv_algEquiv (y : IdeleClassGroup (𝓞 E) E) :
    ideleClassNorm (K := F) (L := E') (ideleClassEquiv φ.toRingEquiv y) =
      ideleClassNorm (K := F) (L := E) y := by
  let : Fintype (E ≃ₐ[F] E) := Fintype.ofFinite _
  let : Fintype (E' ≃ₐ[F] E') := Fintype.ofFinite _
  apply (ideleClassGaloisDescent F E').1
  rw [ideleClassNormGaloisProduct F E', ← ideleClassEquiv_algEquiv_ideleClassInclusion φ,
    ideleClassNormGaloisProduct F E, map_prod]
  exact (Fintype.prod_equiv (AlgEquiv.autCongr φ).toEquiv
    (fun σ => ideleClassEquiv φ.toRingEquiv (relativeIdeleClassAut F E σ y))
    (fun τ => relativeIdeleClassAut F E' τ (ideleClassEquiv φ.toRingEquiv y))
    fun σ => (relativeIdeleClassAut_autCongr φ σ y).symm).symm

include φ in
/-- The two extension fields have the same idele-class norm image in `C_F`. -/
theorem range_ideleClassNorm_algEquiv :
    Set.range (ideleClassNorm (K := F) (L := E')) =
      Set.range (ideleClassNorm (K := F) (L := E)) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨ideleClassEquiv φ.symm.toRingEquiv y,
      ideleClassNorm_ideleClassEquiv_algEquiv φ.symm y⟩
  · rintro ⟨y, rfl⟩
    exact ⟨ideleClassEquiv φ.toRingEquiv y, ideleClassNorm_ideleClassEquiv_algEquiv φ y⟩

end Transport

section InertiaTransport

variable {F : Type u} {E : Type v} {E' : Type w} [Field F] [NumberField F]
  [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra F E] [Algebra F E']
  (φ : E' ≃ₐ[F] E)

/-- Pulling a place of `E` back to `E'` along `φ` preserves its inertia degree over `F`. -/
theorem inertiaDeg_finitePlaceEquiv_algEquiv (p : HeightOneSpectrum (𝓞 F))
    (q : HeightOneSpectrum (𝓞 E)) [q.asIdeal.LiesOver p.asIdeal] :
    (finitePlaceEquiv φ.toRingEquiv q).asIdeal.inertiaDeg (𝓞 F) =
      q.asIdeal.inertiaDeg (𝓞 F) := by
  have := liesOver_finitePlaceEquiv_algEquiv φ p q
  have hp : p.asIdeal.IsMaximal := p.isMaximal
  have hq : q.asIdeal.IsMaximal := q.isMaximal
  have hq' : (finitePlaceEquiv φ.toRingEquiv q).asIdeal.IsMaximal :=
    (finitePlaceEquiv φ.toRingEquiv q).isMaximal
  rw [Ideal.inertiaDeg_eq_of_isMaximal p.asIdeal, Ideal.inertiaDeg_eq_of_isMaximal p.asIdeal]
  exact (Ideal.Quotient.algEquivOfEqComap p.asIdeal (RingOfIntegers.mapAlgEquiv φ)
    rfl).toLinearEquiv.finrank_eq

end InertiaTransport

/-- A finite separable extension is isomorphic to an extension in the universe of its base. -/
theorem exists_algEquiv_baseUniverse (F : Type u) (E : Type v) [Field F] [Field E]
    [Algebra F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] :
    ∃ (E' : Type u) (_ : Field E') (_ : Algebra F E'), Nonempty (E ≃ₐ[F] E') := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element F E
  have hint : IsIntegral F α := .of_finite F α
  have : Fact (Irreducible (minpoly F α)) := ⟨minpoly.irreducible hint⟩
  exact ⟨AdjoinRoot (minpoly F α), inferInstance, inferInstance,
    ⟨((IntermediateField.adjoinRootEquivAdjoin F hint).trans
      ((IntermediateField.equivOfEq hα).trans IntermediateField.topEquiv)).symm⟩⟩

/-! ### The same-universe calculation through the relative Weil group -/

section SameUniverse

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E] [IsCyclic (E ≃ₐ[F] E)]

/-- At a place `w ∣ z` of ramification index one, some `a ∈ F_zˣ` of valuation `exp (-1)`
has the following property: the `k`-th power of its idele class is a norm from `C_E`
exactly when the inertia degree of `w` divides `k`. -/
theorem exists_pow_mem_range_ideleClassNorm_iff
    (z : FinitePlace F) (w : FinitePlace E) [w.asIdeal.LiesOver z.asIdeal]
    (he : w.asIdeal.ramificationIdx (𝓞 F) = 1) :
    ∃ a : (z.adicCompletion F)ˣ, Valued.v (a : z.adicCompletion F) = WithZero.exp (-1 : ℤ) ∧
      ∀ k : ℕ, IdeleClassGroup.ofAdicCompletion (𝓞 F) F z a ^ k ∈
          Set.range (ideleClassNorm (K := F) (L := E)) ↔
        w.asIdeal.inertiaDeg (𝓞 F) ∣ k := by
  choose I hI using localRelativeClassFormation.{u}
  have hI' : ∀ (p : ℕ) [Fact p.Prime],
      (I p).RelativeClassFormation ∧ (I p).ArithmeticNormalization :=
    fun p _ => ⟨(hI p).2.1, (hI p).1⟩
  obtain ⟨c, hc⟩ := fundamentalClass_exists I hI'
  obtain ⟨-, hker⟩ := RelativeWeilGroup.relativeWeilTransferReciprocity I hI' c hc F E
  obtain ⟨e, he', -⟩ := LocalClassField.geometricWeilReciprocityExistenceUniqueness
    (residuePrime z) (towerPadicField z w) (towerPadicField z w).canonicalTopologicalData
  obtain ⟨ι, hι⟩ := localRelativeWeilMapExistence I hI' c hc F E z w e he'
  have hι' : ∀ (g : Weil.Local.localWeilGroup (padicField z)) (x : E),
      RelativeWeilGroup.closurePlaceEmbedding z w
          (RelativeWeilGroup.projection c F E (ι.toMonoidHom g) x) =
        AlgEquiv.toAlgHom (Weil.Local.localProjection (padicField z) g)
          (RelativeWeilGroup.closurePlaceEmbedding z w x) := hι.2.1
  let y := Weil.Local.localGeometricFrobenius (padicField z)
  have hy : Weil.Local.localDegree (padicField z) y = Multiplicative.ofAdd (1 : ℤ) :=
    Weil.Local.localGeometricFrobenius_degree (padicField z)
  obtain ⟨a, ha, htr⟩ := RelativeWeilGroup.exists_transfer_eq_inv_ofAdicCompletion c z w hc.2.1
    he e ι hι y hy
  refine ⟨a, ha, fun k => ?_⟩
  let N := Set.range (ideleClassNorm (K := F) (L := E))
  let transfer := RelativeWeilGroup.transfer c F E
  let projection := RelativeWeilGroup.projection c F E
  let inclusion := RelativeWeilGroup.inclusion c F E
  have hle : transfer.ker ≤ projection.ker :=
    hker.le.trans (Abelianization.commutator_subset_ker projection)
  have hexact : inclusion.range = projection.ker := RelativeWeilGroup.exact c F E
  -- The transfer of `t` is a norm exactly when `t` projects to the identity.
  have hnorm : ∀ t, transfer t ∈ N ↔ projection t = 1 := by
    intro t
    constructor
    · rintro ⟨b, hb⟩
      have h1 : t * (inclusion b)⁻¹ ∈ transfer.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv]
        change transfer t *
          (RelativeWeilGroup.transfer c F E (RelativeWeilGroup.inclusion c F E b))⁻¹ = 1
        rw [RelativeWeilGroup.transfer_inclusion, hb, mul_inv_cancel]
      have h2 : inclusion b ∈ projection.ker := by
        rw [← hexact]
        exact ⟨b, rfl⟩
      have h3 := hle h1
      rw [MonoidHom.mem_ker, map_mul, map_inv, MonoidHom.mem_ker.mp h2, inv_one,
        mul_one] at h3
      exact h3
    · intro ht
      have ht' : t ∈ inclusion.range := by
        rw [hexact]
        exact ht
      obtain ⟨b, rfl⟩ := ht'
      exact ⟨b, (RelativeWeilGroup.transfer_inclusion c F E b).symm⟩
  have hinv : ∀ u, u⁻¹ ∈ N ↔ u ∈ N := by
    intro u
    constructor
    · rintro ⟨b, hb⟩
      exact ⟨b⁻¹, by rw [map_inv, hb]; exact inv_inv u⟩
    · rintro ⟨b, hb⟩
      exact ⟨b⁻¹, by rw [map_inv, hb]⟩
  have hdeg : Weil.Local.localDegreeInt (padicField z) (y ^ k) = k := by
    unfold Weil.Local.localDegreeInt
    rw [map_pow, hy, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, mul_one]
  rw [← extensionResidueDegree_completionPadicAlgHom z w]
  calc IdeleClassGroup.ofAdicCompletion (𝓞 F) F z a ^ k ∈ N
        ↔ transfer (ι (y ^ k)) ∈ N := by
          rw [map_pow, map_pow]
          change _ ↔ RelativeWeilGroup.transfer c F E (ι y) ^ k ∈ N
          rw [htr, inv_pow, hinv]
    _ ↔ projection (ι (y ^ k)) = 1 := hnorm _
    _ ↔ ι.toMonoidHom (y ^ k) ∈ RelativeWeilGroup.ideleClassSubgroup c F E := by
          rw [RelativeWeilGroup.ideleClassSubgroup, hexact]
          rfl
    _ ↔ y ^ k ∈ (RelativeWeilGroup.completionWeilMap z w).toMonoidHom.range :=
          RelativeWeilGroup.mem_ideleClassSubgroup_iff c z w hc.2.1 ι.toMonoidHom hι' (y ^ k)
    _ ↔ _ := by
          rw [RelativeWeilGroup.mem_completionWeilMap_range_iff z w he, hdeg]
          exact Int.natCast_dvd_natCast

/-- Same-universe form of the local order: at an unramified place `z` of `η` and a place
`w ∣ z` of ramification index one, `η_z(ϖ_z)` has order the inertia degree of `w`. -/
theorem orderOf_finiteUniformizerValue_of_sameUniverse (η : HeckeCharacter F)
    (hη : η.HasNormKernel E) (z : FinitePlace F) (hz : η.IsUnramifiedAt z)
    (w : FinitePlace E) [w.asIdeal.LiesOver z.asIdeal]
    (he : w.asIdeal.ramificationIdx (𝓞 F) = 1) :
    orderOf (η.finiteUniformizerValue z) = w.asIdeal.inertiaDeg (𝓞 F) := by
  obtain ⟨a, ha, hk⟩ := exists_pow_mem_range_ideleClassNorm_iff z w he
  have hval : η (IdeleClassGroup.ofAdicCompletion (𝓞 F) F z a) = η.finiteUniformizerValue z :=
    η.finiteComponent_eq_finiteUniformizerValue z hz a ha
  rw [← hval]
  set x := IdeleClassGroup.ofAdicCompletion (𝓞 F) F z a
  have hpow : ∀ k : ℕ, η x ^ k = 1 ↔ w.asIdeal.inertiaDeg (𝓞 F) ∣ k := by
    intro k
    rw [← map_pow, hη, hk]
  apply Nat.dvd_antisymm
  · exact orderOf_dvd_of_pow_eq_one ((hpow _).mpr dvd_rfl)
  · exact (hpow _).mp (pow_orderOf_eq_one _)

end SameUniverse

/-- **The local order of a cyclic norm-kernel character.** Outside finitely many finite
places, `η` is unramified, every place above has ramification index one, and the value of
`η` at a uniformizer has order the residue degree of each place above. -/
theorem cyclicNormKernelUnramifiedOrder : CyclicNormKernelUnramifiedOrderStatement.{uF, uE} := by
  intro F E _ _ _ _ _ _ _ η hη
  obtain ⟨E', _, _, ⟨φ⟩⟩ := exists_algEquiv_baseUniverse F E
  have : NumberField E' := NumberField.of_ringEquiv (K := E) (L := E') φ.toRingEquiv
  have : IsGalois F E' := IsGalois.of_algEquiv φ
  have : IsCyclic (E' ≃ₐ[F] E') := (AlgEquiv.autCongr φ).isCyclic.mp inferInstance
  have hη' : η.HasNormKernel E' := fun x => by
    rw [range_ideleClassNorm_algEquiv φ]
    exact hη x
  obtain ⟨S, hS⟩ := HeckeFunctionalEquation.exists_finset_isUnramifiedAt (K := F) η
  filter_upwards [eventually_ramificationIdx_eq_one F E, eventually_ramificationIdx_eq_one F E',
    S.eventually_cofinite_notMem] with v hE hE' hvS
  refine ⟨hS v hvS, fun q => ⟨hE q.1 q.2, ?_⟩⟩
  have := liesOver_finitePlaceEquiv_algEquiv φ.symm v q.1
  rw [← inertiaDeg_finitePlaceEquiv_algEquiv φ.symm v q.1]
  exact orderOf_finiteUniformizerValue_of_sameUniverse η hη' v (hS v hvS)
    (finitePlaceEquiv φ.symm.toRingEquiv q.1) (hE' _ this)

end Langlands.Global.HeckeCharacter
