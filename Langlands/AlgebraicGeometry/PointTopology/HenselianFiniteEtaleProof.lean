import Langlands.AlgebraicGeometry.PointTopology.HenselianTensorCompletionFieldProof
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.Pi

/-!
# Base change of finite étale algebras to the completion of a henselian field

Let `K` be separably algebraically closed in a field `F` (for a henselian valued field, `F` is
the completion). For finite étale `K`-algebras `A` and `B`, base change
`φ ↦ id_F ⊗ φ` is a bijection from `K`-algebra maps `A → B` to `F`-algebra maps
`F ⊗ A → F ⊗ B`.

The key fact: a root in `F ⊗_K B` of a separable polynomial over `K` comes from `B`. For a field
`B = M`, put `y` together with `M` in the subfield `N = K(y) ⊔ M` of the field `F ⊗_K M`. Then
`F ⊗_K N` is a field mapping injectively into `F ⊗_K M`. Comparing dimensions gives `N = M`.
A general `B` is a finite product of such fields.
-/

noncomputable section

universe u

open Polynomial IntermediateField
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.PointTopology

namespace HenselianFiniteEtale

variable {K F : Type u} [Field K] [Field F] [Algebra K F]

/-- In a field `E` over `F` of dimension `[M : K]` that contains `M`, a root of a separable
polynomial over `K` lies in `M`. -/
theorem mem_range_of_aeval_eq_zero (hsep : separableClosure K F = ⊥) {M E : Type u} [Field M]
    [Algebra K M] [FiniteDimensional K M] [Algebra.IsSeparable K M] [Field E] [Algebra F E]
    [Algebra K E] [IsScalarTower K F E] [FiniteDimensional F E] (φ : M →ₐ[K] E)
    (hdim : Module.finrank F E = Module.finrank K M) {p : K[X]} (hp : p.Separable) {y : E}
    (hy : aeval y p = 0) : y ∈ Set.range φ := by
  have hyint : IsIntegral K y := (show IsAlgebraic K y from ⟨p, hp.ne_zero, hy⟩).isIntegral
  have hys : IsSeparable K y := hp.of_dvd (minpoly.dvd K y hy)
  let eM : M ≃ₐ[K] φ.fieldRange := AlgEquiv.ofInjectiveField φ
  have : FiniteDimensional K K⟮y⟯ := IntermediateField.adjoin.finiteDimensional hyint
  have : FiniteDimensional K φ.fieldRange := LinearEquiv.finiteDimensional eM.toLinearEquiv
  have : Algebra.IsSeparable K K⟮y⟯ :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable K E).2 hys
  have : Algebra.IsSeparable K φ.fieldRange := AlgEquiv.Algebra.isSeparable eM
  let N : IntermediateField K E := K⟮y⟯ ⊔ φ.fieldRange
  have hfield : IsField (F ⊗[K] N) := HenselianTensorCompletion.isField_tensor hsep
  let μ : F ⊗[K] N →ₐ[F] E :=
    Algebra.TensorProduct.lift (Algebra.ofId F E) N.val (fun _ _ => Commute.all _ _)
  have hμ : Function.Injective μ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    obtain ⟨x', hx'⟩ := hfield.mul_inv_cancel hx0
    have h1 := congrArg μ hx'
    rw [map_mul, hx, zero_mul] at h1
    exact zero_ne_one (h1.trans μ.map_one)
  have hle : Module.finrank F (F ⊗[K] N) ≤ Module.finrank F E :=
    LinearMap.finrank_le_finrank_of_injective (f := μ.toLinearMap) hμ
  rw [Module.finrank_baseChange, hdim, eM.toLinearEquiv.finrank_eq] at hle
  have hrange : φ.fieldRange = N := IntermediateField.eq_of_le_of_finrank_le le_sup_right hle
  have hyN : y ∈ N := le_sup_left (a := K⟮y⟯) (IntermediateField.mem_adjoin_simple_self K y)
  rw [← hrange] at hyN
  exact hyN

/-- For a finite separable field extension `M`, a root in `F ⊗_K M` of a separable polynomial
over `K` comes from `M`. -/
theorem exists_tmul_eq_of_field (hsep : separableClosure K F = ⊥) {M : Type u} [Field M]
    [Algebra K M] [FiniteDimensional K M] [Algebra.IsSeparable K M] {p : K[X]}
    (hp : p.Separable) {y : F ⊗[K] M} (hy : aeval y p = 0) : ∃ m : M, (1 : F) ⊗ₜ m = y := by
  let pb := Field.powerBasisOfFiniteOfSeparable K M
  have hint : IsIntegral K pb.gen := pb.isIntegral_gen
  have hirr' := HenselianTensorCompletion.irreducible_map hsep (minpoly.monic hint)
    (minpoly.irreducible hint) (Algebra.IsSeparable.isSeparable K pb.gen)
  have : Fact (Irreducible ((minpoly K pb.gen).map (algebraMap K F))) := ⟨hirr'⟩
  have hroot : aeval (AdjoinRoot.root ((minpoly K pb.gen).map (algebraMap K F)))
      (minpoly K pb.gen) = 0 := by
    rw [← Polynomial.aeval_map_algebraMap F, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  let φL : M →ₐ[K] AdjoinRoot ((minpoly K pb.gen).map (algebraMap K F)) := pb.lift _ hroot
  let Φ : F ⊗[K] M →ₐ[F] AdjoinRoot ((minpoly K pb.gen).map (algebraMap K F)) :=
    Algebra.TensorProduct.lift (Algebra.ofId F _) φL (fun _ _ => Commute.all _ _)
  have hsurj : Function.Surjective Φ := by
    have hrange : Φ.range = ⊤ := by
      rw [eq_top_iff, ← AdjoinRoot.adjoinRoot_eq_top, Algebra.adjoin_le_iff,
        Set.singleton_subset_iff]
      refine ⟨1 ⊗ₜ pb.gen, ?_⟩
      simp [Φ, φL, PowerBasis.lift_gen]
    intro x
    have hx : x ∈ Φ.range := hrange ▸ Algebra.mem_top
    exact hx
  have := (AdjoinRoot.powerBasis hirr'.ne_zero).finite
  have hdimE : Module.finrank F (AdjoinRoot ((minpoly K pb.gen).map (algebraMap K F))) =
      Module.finrank K M := by
    rw [(AdjoinRoot.powerBasis hirr'.ne_zero).finrank, AdjoinRoot.powerBasis_dim, natDegree_map,
      pb.finrank, pb.natDegree_minpoly]
  have hdim : Module.finrank F (F ⊗[K] M) =
      Module.finrank F (AdjoinRoot ((minpoly K pb.gen).map (algebraMap K F))) := by
    rw [Module.finrank_baseChange, hdimE]
  have hinj : Function.Injective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim (f := Φ.toLinearMap)).mpr hsurj
  have hΦ1 : ∀ m : M, Φ (1 ⊗ₜ m) = φL m := fun m => by
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  have hy' : aeval (Φ y) p = 0 := by
    rw [show Φ y = (Φ.restrictScalars K) y from rfl, aeval_algHom_apply, hy, map_zero]
  obtain ⟨m, hm⟩ := mem_range_of_aeval_eq_zero hsep φL hdimE hp hy'
  exact ⟨m, hinj (by rw [hΦ1, hm])⟩

/-- For a finite étale `B`, a root in `F ⊗_K B` of a separable polynomial over `K` comes from
`B`. -/
theorem exists_tmul_eq (hsep : separableClosure K F = ⊥) {B : Type u} [CommRing B]
    [Algebra K B] [Algebra.Etale K B] {p : K[X]} (hp : p.Separable) {y : F ⊗[K] B}
    (hy : aeval y p = 0) : ∃ b : B, (1 : F) ⊗ₜ b = y := by
  classical
  obtain ⟨I, _, Mi, _, _, e, hMi⟩ := (Algebra.Etale.iff_exists_algEquiv_prod K B).mp inferInstance
  have : Fintype I := Fintype.ofFinite I
  let T : F ⊗[K] B ≃ₐ[F] ∀ i, F ⊗[K] Mi i :=
    (Algebra.TensorProduct.congr AlgEquiv.refl e).trans
      (Algebra.TensorProduct.piRight K F F Mi)
  have hTy : ∀ i, aeval (T y i) p = 0 := fun i => by
    have h := aeval_algHom_apply
      ((Pi.evalAlgHom K (fun i => F ⊗[K] Mi i) i).comp (T.toAlgHom.restrictScalars K)) y p
    rw [hy, map_zero] at h
    exact h
  have hm : ∀ i, ∃ m : Mi i, (1 : F) ⊗ₜ m = T y i := fun i => by
    have := (hMi i).1
    have := (hMi i).2
    exact exists_tmul_eq_of_field hsep hp (hTy i)
  choose m hm using hm
  refine ⟨e.symm m, T.injective ?_⟩
  funext i
  rw [← hm i]
  simp [T]

/-- A separable polynomial over `K` kills each element of a finite étale `K`-algebra. -/
theorem exists_separable_aeval_eq_zero {A : Type u} [CommRing A] [Algebra K A]
    [Algebra.Etale K A] (a : A) : ∃ p : K[X], p.Separable ∧ aeval a p = 0 := by
  classical
  obtain ⟨I, _, Ai, _, _, e, hAi⟩ := (Algebra.Etale.iff_exists_algEquiv_prod K A).mp inferInstance
  have : Fintype I := Fintype.ofFinite I
  have hint : ∀ i, IsIntegral K (e a i) := fun i => by
    have := (hAi i).1
    exact .of_finite K _
  let s : Finset K[X] := Finset.univ.image fun i => minpoly K (e a i)
  have hs : ∀ q ∈ s, ∃ i, minpoly K (e a i) = q := fun q hq => by
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hq
    exact ⟨i, hi⟩
  refine ⟨∏ q ∈ s, q, ?_, ?_⟩
  · refine separable_prod' (fun q hq q' hq' hne => ?_) (fun q hq => ?_)
    · obtain ⟨i, rfl⟩ := hs q hq
      obtain ⟨j, rfl⟩ := hs q' hq'
      refine ((minpoly.irreducible (hint i)).coprime_iff_not_dvd).mpr fun hdvd => hne ?_
      exact eq_of_monic_of_associated (minpoly.monic (hint i)) (minpoly.monic (hint j))
        ((minpoly.irreducible (hint i)).associated_of_dvd (minpoly.irreducible (hint j)) hdvd)
    · obtain ⟨i, rfl⟩ := hs q hq
      have := (hAi i).2
      exact Algebra.IsSeparable.isSeparable K (e a i)
  · apply e.injective
    rw [map_zero]
    funext i
    have h := aeval_algHom_apply ((Pi.evalAlgHom K Ai i).comp e.toAlgHom) a (∏ q ∈ s, q)
    have h2 : aeval (e a i) (∏ q ∈ s, q) = 0 := by
      rw [map_prod]
      exact Finset.prod_eq_zero (Finset.mem_image_of_mem _ (Finset.mem_univ i)) (minpoly.aeval K _)
    exact h.symm.trans h2

/-- **Base change is bijective on algebra maps between finite étale algebras.** -/
theorem bijective_map (hsep : separableClosure K F = ⊥) {A B : Type u} [CommRing A]
    [Algebra K A] [Algebra.Etale K A] [CommRing B] [Algebra K B] [Algebra.Etale K B] :
    Function.Bijective (fun φ : A →ₐ[K] B => Algebra.TensorProduct.map (AlgHom.id F F) φ) := by
  have hinj : Function.Injective (Algebra.TensorProduct.includeRight : B →ₐ[K] F ⊗[K] B) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap K F).injective
  constructor
  · intro φ φ' h
    ext a
    apply hinj
    have := congrArg (fun ψ : F ⊗[K] A →ₐ[F] F ⊗[K] B => ψ (1 ⊗ₜ a)) h
    simpa using this
  · intro ψ
    let ψ' : A →ₐ[K] F ⊗[K] B := (ψ.restrictScalars K).comp Algebra.TensorProduct.includeRight
    have hmem : ∀ a, ψ' a ∈ (Algebra.TensorProduct.includeRight : B →ₐ[K] F ⊗[K] B).range := by
      intro a
      obtain ⟨p, hp, hpa⟩ := exists_separable_aeval_eq_zero (K := K) a
      obtain ⟨b, hb⟩ := exists_tmul_eq hsep hp (y := ψ' a)
        (by rw [aeval_algHom_apply, hpa, map_zero])
      exact ⟨b, hb⟩
    let eB := AlgEquiv.ofInjective _ hinj
    let φ : A →ₐ[K] B := (eB.symm : _ →ₐ[K] B).comp (ψ'.codRestrict _ hmem)
    have hφ : ∀ a, (1 : F) ⊗ₜ[K] φ a = ψ (1 ⊗ₜ a) := by
      intro a
      have := congrArg Subtype.val (eB.apply_symm_apply (ψ'.codRestrict _ hmem a))
      rw [AlgEquiv.ofInjective_apply] at this
      exact this
    refine ⟨φ, Algebra.TensorProduct.ext' fun c a => ?_⟩
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      show c ⊗ₜ[K] a = c • ((1 : F) ⊗ₜ[K] a) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
      map_smul, ← hφ, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- A `K`-embedding of a finite separable `L` into a field `E` over `F` of the same dimension
identifies `F ⊗_K L` with `E`. -/
theorem nonempty_algEquiv_of_algHom (hsep : separableClosure K F = ⊥) {L E : Type u} [Field L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L] [Field E] [Algebra F E]
    [Algebra K E] [IsScalarTower K F E] [FiniteDimensional F E] (j : L →ₐ[K] E)
    (hdim : Module.finrank K L = Module.finrank F E) : Nonempty (F ⊗[K] L ≃ₐ[F] E) := by
  have hfield : IsField (F ⊗[K] L) := HenselianTensorCompletion.isField_tensor hsep
  let μ : F ⊗[K] L →ₐ[F] E := Algebra.TensorProduct.lift (Algebra.ofId F E) j
    (fun _ _ => Commute.all _ _)
  have hμ : Function.Injective μ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    obtain ⟨x', hx'⟩ := hfield.mul_inv_cancel hx0
    have h1 := congrArg μ hx'
    rw [map_mul, hx, zero_mul] at h1
    exact zero_ne_one (h1.trans μ.map_one)
  have hd : Module.finrank F (F ⊗[K] L) = Module.finrank F E := by
    rw [Module.finrank_baseChange, hdim]
  have hsurj : Function.Surjective μ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd (f := μ.toLinearMap)).mp hμ
  exact ⟨AlgEquiv.ofBijective μ ⟨hμ, hsurj⟩⟩

/-- Essential surjectivity of base change reduces to finite separable field extensions. -/
theorem exists_etale_of_field
    (hfield : ∀ (E : Type u) [Field E] [Algebra F E] [FiniteDimensional F E]
      [Algebra.IsSeparable F E], ∃ (L : Type u) (_ : Field L) (_ : Algebra K L),
        FiniteDimensional K L ∧ Algebra.IsSeparable K L ∧ Nonempty (F ⊗[K] L ≃ₐ[F] E))
    (E : Type u) [CommRing E] [Algebra F E] [Algebra.Etale F E] [Module.Finite F E] :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra K A), Algebra.Etale K A ∧ Module.Finite K A ∧
      Nonempty (F ⊗[K] A ≃ₐ[F] E) := by
  classical
  obtain ⟨I, _, Ei, _, _, e, hEi⟩ := (Algebra.Etale.iff_exists_algEquiv_prod F E).mp inferInstance
  have : Fintype I := Fintype.ofFinite I
  have h : ∀ i, ∃ (L : Type u) (_ : Field L) (_ : Algebra K L), FiniteDimensional K L ∧
      Algebra.IsSeparable K L ∧ Nonempty (F ⊗[K] L ≃ₐ[F] Ei i) := fun i => by
    have := (hEi i).1
    have := (hEi i).2
    exact hfield (Ei i)
  choose L hLf hLa hLfin hLsep hLe using h
  let _ : ∀ i, Field (L i) := hLf
  let _ : ∀ i, Algebra K (L i) := hLa
  have : ∀ i, Module.Finite K (L i) := hLfin
  refine ⟨∀ i, L i, inferInstance, inferInstance, ?_, inferInstance, ?_⟩
  · exact (Algebra.Etale.iff_exists_algEquiv_prod K _).mpr
      ⟨I, inferInstance, L, hLf, hLa, AlgEquiv.refl, fun i => ⟨hLfin i, hLsep i⟩⟩
  · exact ⟨(Algebra.TensorProduct.piRight K F F L).trans
      ((AlgEquiv.piCongrRight fun i => (hLe i).some).trans e.symm)⟩

end HenselianFiniteEtale

end Langlands.AlgebraicGeometry.PointTopology
