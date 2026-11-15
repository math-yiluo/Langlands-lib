import Langlands.GroupScheme.IntegralModel.GreenbergMixed.GroupModel
import Langlands.GroupScheme.GeometricConnectedness
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Connectedness of Greenberg groups

If `X` is a smooth affine group over `R` with geometrically connected fibres and the residue
field `k` is algebraically closed, then its Greenberg group is connected, hence geometrically
connected. An idempotent `e` of the representing algebra takes the same value at all
`k`-points: points over `k[t]` connect any two `k`-points with the same reduction (lifted by
formal smoothness along the nilpotent thickening of interpolated coordinates), and a lift of
the generic point of the special fibre `X_k` along `ℛ(D) → D` (with `D = k ⊗ O(X)`, which has
no nontrivial idempotents) reaches every reduction. The Nullstellensatz then forces `e = 0`
or `e = 1`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry Limits
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.IntegralModel.GreenbergMixed

section Idempotents

/-- A connected spectrum has only the trivial idempotents. -/
theorem eq_zero_or_one_of_connectedSpace {A : Type u} [CommRing A]
    [ConnectedSpace (PrimeSpectrum A)] {e : A} (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  have hcl : IsClopen (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum A)) :=
    PrimeSpectrum.isClopen_iff.2 ⟨e, he, rfl⟩
  have hnil : ∀ x : A, IsIdempotentElem x → IsNilpotent x → x = 0 := by
    intro x hx ⟨m, hm⟩
    rw [← hx.pow_succ_eq m, pow_succ, hm, zero_mul]
  rcases isClopen_iff.1 hcl with h | h
  · left
    apply hnil e he
    rw [← PrimeSpectrum.basicOpen_eq_bot_iff]
    exact TopologicalSpace.Opens.ext h
  · right
    have h1 : IsNilpotent (1 - e) := by
      rw [← PrimeSpectrum.basicOpen_eq_bot_iff]
      apply TopologicalSpace.Opens.ext
      rw [← PrimeSpectrum.zeroLocus_eq_basicOpen_of_isIdempotentElem e he]
      change PrimeSpectrum.zeroLocus {e} = ∅
      have : (PrimeSpectrum.zeroLocus {e} : Set (PrimeSpectrum A)) =
          (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum A))ᶜ := by
        ext p
        simp [PrimeSpectrum.mem_zeroLocus]
      rw [this, h, Set.compl_univ]
    have := hnil (1 - e) he.one_sub h1
    rw [sub_eq_zero] at this
    exact this.symm

/-- A nontrivial ring with only trivial idempotents has a connected spectrum. -/
theorem connectedSpace_of_idempotents {A : Type u} [CommRing A] [Nontrivial A]
    (h : ∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1) : ConnectedSpace (PrimeSpectrum A) := by
  have : PreconnectedSpace (PrimeSpectrum A) := by
    rw [preconnectedSpace_iff_clopen]
    intro s hs
    obtain ⟨e, he, rfl⟩ := PrimeSpectrum.isClopen_iff.1 hs
    rcases h e he with rfl | rfl
    · left
      rw [PrimeSpectrum.basicOpen_zero]
      rfl
    · right
      rw [PrimeSpectrum.basicOpen_one]
      rfl
  exact ⟨inferInstance⟩

/-- **Nullstellensatz form.** Over an algebraically closed field, an element of a finitely
generated algebra vanishing at all rational points is nilpotent. -/
theorem isNilpotent_of_forall_algHom {K : Type*} [Field K] [IsAlgClosed K] {σ : Type*}
    [Finite σ] (I : Ideal (MvPolynomial σ K)) (b : MvPolynomial σ K ⧸ I)
    (h : ∀ ψ : (MvPolynomial σ K ⧸ I) →ₐ[K] K, ψ b = 0) : IsNilpotent b := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
  have hp : p ∈ MvPolynomial.vanishingIdeal K (MvPolynomial.zeroLocus K I) := by
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    intro x hx
    have := h (Ideal.Quotient.liftₐ I (MvPolynomial.aeval x) fun q hq => hx q hq)
    simpa using this
  rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical] at hp
  obtain ⟨m, hm⟩ := hp
  exact ⟨m, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact hm⟩

/-- Kernels contained in nilpotent ideals after an injective map are nilpotent. -/
theorem isNilpotent_ker_of_injective {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (g : A →+* C) (i : A →+* B) (hi : Function.Injective i) {J : Ideal B}
    (hJ : IsNilpotent J) (h : ∀ x, g x = 0 → i x ∈ J) : IsNilpotent (RingHom.ker g) := by
  obtain ⟨m, hm⟩ := hJ
  refine ⟨m, ?_⟩
  have hle : Ideal.map i (RingHom.ker g) ≤ J := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact h x hx
  have : Ideal.map i (RingHom.ker g ^ m) = ⊥ := by
    rw [Ideal.map_pow]
    exact le_bot_iff.1 ((Ideal.pow_right_mono hle m).trans (le_of_eq hm))
  exact (Ideal.map_eq_bot_iff_of_injective hi).1 this

end Idempotents


section Paths

variable {R : Type u} [CommRing R] [IsLocalRing R] {n : ℕ+} (ℛ : GreenbergRingScheme R n)

local notation "k" => IsLocalRing.ResidueField R
local notation "κ" => CommRingCat.of (IsLocalRing.ResidueField R)

namespace GreenbergRingScheme

/-- Evaluation of polynomials at a point of `k`. -/
abbrev evAt (a : k) : CommAlgCat.of κ (Polynomial k) ⟶ CommAlgCat.of κ k :=
  CommAlgCat.ofHom (Polynomial.aeval a)

/-- Pairs of points of `ℛ(k)` with equal reduction. -/
def pairAlg : Subalgebra R
    (ℛ.functor.obj (CommAlgCat.of κ k) × ℛ.functor.obj (CommAlgCat.of κ k)) :=
  AlgHom.equalizer ((ℛ.redₐ k).comp (AlgHom.fst R _ _)) ((ℛ.redₐ k).comp (AlgHom.snd R _ _))

/-- Points of `ℛ(k[t])` whose reduction is a constant polynomial. -/
def constAlg : Subalgebra R (ℛ.functor.obj (CommAlgCat.of κ (Polynomial k))) :=
  Subalgebra.comap (ℛ.redₐ (Polynomial k))
    ((⊥ : Subalgebra k (Polynomial k)).restrictScalars R)

theorem mem_constAlg_iff (x : ℛ.functor.obj (CommAlgCat.of κ (Polynomial k))) :
    x ∈ ℛ.constAlg ↔ ∃ c : k, Polynomial.C c = ℛ.red _ x := by
  change ℛ.redₐ (Polynomial k) x ∈ (⊥ : Subalgebra k (Polynomial k)) ↔ _
  rw [Algebra.mem_bot]
  rfl

theorem red_evAt (a : k) (x : ℛ.functor.obj (CommAlgCat.of κ (Polynomial k))) :
    ℛ.red _ ((ℛ.functor.map (evAt a)).hom x) = Polynomial.aeval a (ℛ.red _ x) :=
  ℛ.red_map _ x

/-- The endpoint map `x ↦ (x(0), x(1))`. -/
def endpoints : ℛ.constAlg →ₐ[R] ℛ.pairAlg :=
  AlgHom.codRestrict (((ℛ.functor.map (evAt 0)).hom.prod (ℛ.functor.map (evAt 1)).hom).comp
    ℛ.constAlg.val) ℛ.pairAlg (by
      rintro ⟨x, hx⟩
      obtain ⟨c, hc⟩ := (ℛ.mem_constAlg_iff x).1 hx
      rw [pairAlg, AlgHom.mem_equalizer]
      change ℛ.red _ ((ℛ.functor.map (evAt 0)).hom x) =
        ℛ.red _ ((ℛ.functor.map (evAt 1)).hom x)
      rw [red_evAt, red_evAt, ← hc, Polynomial.aeval_C, Polynomial.aeval_C])

theorem endpoints_val (x : ℛ.constAlg) :
    (ℛ.endpoints x).val = ((ℛ.functor.map (evAt 0)).hom x.val,
      (ℛ.functor.map (evAt 1)).hom x.val) := rfl

/-- Linear interpolation of coordinates connects any two points with equal reduction. -/
theorem endpoints_surjective : Function.Surjective ℛ.endpoints := by
  rintro ⟨⟨a, a'⟩, hp⟩
  have hp' : ℛ.red _ a = ℛ.red _ a' := (AlgHom.mem_equalizer _ _ _).1 hp
  obtain ⟨c, hc⟩ := ℛ.red_coord
  let x : ℛ.functor.obj (CommAlgCat.of κ (Polynomial k)) := (ℛ.coord _).symm fun j =>
    Polynomial.C (ℛ.coord _ a j) * (1 - Polynomial.X) +
      Polynomial.C (ℛ.coord _ a' j) * Polynomial.X
  have hx : ℛ.red _ x = Polynomial.C (ℛ.red _ a) * (1 - Polynomial.X) +
      Polynomial.C (ℛ.red _ a') * Polynomial.X := by
    rw [hc, hc (CommAlgCat.of κ k) a, hc (CommAlgCat.of κ k) a']
    simp only [x, Equiv.apply_symm_apply, map_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [map_mul, Polynomial.algebraMap_eq, Algebra.algebraMap_self, RingHom.id_apply]
    ring
  have hmem : x ∈ ℛ.constAlg := (ℛ.mem_constAlg_iff x).2 ⟨ℛ.red _ a, by rw [hx, hp']; ring⟩
  refine ⟨⟨x, hmem⟩, ?_⟩
  apply Subtype.ext
  rw [endpoints_val]
  refine Prod.ext (ℛ.ext_coord fun j => ?_) (ℛ.ext_coord fun j => ?_)
  · rw [ℛ.coord_map]
    simp [x]
  · rw [ℛ.coord_map]
    simp [x]

/-- The endpoint map has nilpotent kernel. -/
theorem endpoints_ker_nilpotent :
    IsNilpotent (RingHom.ker (ℛ.endpoints : ℛ.constAlg →+* ℛ.pairAlg)) := by
  refine isNilpotent_ker_of_injective _ ℛ.constAlg.val.toRingHom Subtype.val_injective
    (ℛ.ker_red_nilpotent (CommAlgCat.of κ (Polynomial k))) ?_
  rintro ⟨x, hx⟩ h0
  obtain ⟨c, hc⟩ := (ℛ.mem_constAlg_iff x).1 hx
  have h1 : (ℛ.functor.map (evAt 0)).hom x = 0 := congrArg (fun p => p.val.1) h0
  have h2 := congrArg (ℛ.red _) h1
  rw [red_evAt, map_zero, ← hc, Polynomial.aeval_C] at h2
  rw [RingHom.mem_ker]
  change ℛ.red _ x = 0
  rw [← hc]
  simpa using h2

variable {O : CommAlgCat.{u} (CommRingCat.of R)} {N : ℕ} {f : MvPolynomial (Fin N) R →ₐ[R] O}
  (hf : Function.Surjective f)

/-- **Paths.** Two `k`-points of the Greenberg algebra whose classified points of `O` have
the same reduction take the same value on every idempotent. -/
theorem idempotent_eq_of_red_eq [Algebra.FormallySmooth R O] {e : ℛ.Poly N ⧸ ℛ.repIdeal f}
    (he : IsIdempotentElem e) (ψ ψ' : ℛ.repAlg f ⟶ CommAlgCat.of κ k)
    (hred : (ℛ.redₐ k).comp (ℛ.classify hf ψ) = (ℛ.redₐ k).comp (ℛ.classify hf ψ')) :
    ψ.hom e = ψ'.hom e := by
  let w : O →ₐ[R] ℛ.pairAlg := AlgHom.codRestrict ((ℛ.classify hf ψ).prod (ℛ.classify hf ψ'))
    ℛ.pairAlg fun x => by
      rw [pairAlg, AlgHom.mem_equalizer]
      exact DFunLike.congr_fun hred x
  let gl := Algebra.FormallySmooth.liftOfSurjective w ℛ.endpoints ℛ.endpoints_surjective
    ℛ.endpoints_ker_nilpotent
  have hgl : ℛ.endpoints.comp gl = w := Algebra.FormallySmooth.comp_liftOfSurjective _ _ _ _
  obtain ⟨χ, hχ⟩ := ℛ.classify_surjective hf (ℛ.constAlg.val.comp gl)
  have h0 : χ ≫ evAt 0 = ψ := by
    apply ℛ.classify_injective hf
    rw [classify_comp, hχ]
    ext x
    exact congrArg (fun p : ℛ.pairAlg => p.val.1) (DFunLike.congr_fun hgl x)
  have h1 : χ ≫ evAt 1 = ψ' := by
    apply ℛ.classify_injective hf
    rw [classify_comp, hχ]
    ext x
    exact congrArg (fun p : ℛ.pairAlg => p.val.2) (DFunLike.congr_fun hgl x)
  have hid : IsIdempotentElem (χ.hom e) := he.map χ.hom
  rw [← h0, ← h1]
  change Polynomial.aeval (0 : k) (χ.hom e) = Polynomial.aeval (1 : k) (χ.hom e)
  rcases IsIdempotentElem.iff_eq_zero_or_one.1 hid with h | h <;> rw [h] <;> simp

end GreenbergRingScheme

end Paths


section Fibre

variable {R : Type u} [CommRing R] [IsLocalRing R] {n : ℕ+} (ℛ : GreenbergRingScheme R n)

local notation "k" => IsLocalRing.ResidueField R
local notation "κ" => CommRingCat.of (IsLocalRing.ResidueField R)

namespace GreenbergRingScheme

variable {O : CommAlgCat.{u} (CommRingCat.of R)} {N : ℕ} {f : MvPolynomial (Fin N) R →ₐ[R] O}
  (hf : Function.Surjective f)

/-- **Constancy on `k`-points.** If the special fibre algebra `k ⊗ O` has only trivial
idempotents, then every idempotent of the representing algebra is constant on `k`-points. -/
theorem idempotent_const [Algebra.FormallySmooth R O] (hf : Function.Surjective f)
    (hD : ∀ d : k ⊗[R] O, IsIdempotentElem d → d = 0 ∨ d = 1)
    {e : ℛ.Poly N ⧸ ℛ.repIdeal f} (he : IsIdempotentElem e) :
    (∀ ψ : ℛ.repAlg f ⟶ CommAlgCat.of κ k, ψ.hom e = 0) ∨
      (∀ ψ : ℛ.repAlg f ⟶ CommAlgCat.of κ k, ψ.hom e = 1) := by
  let u : O →ₐ[R] k ⊗[R] O := Algebra.TensorProduct.includeRight
  let Γ := Algebra.FormallySmooth.liftOfSurjective u (ℛ.redₐ (k ⊗[R] O))
    (ℛ.red_surjective _) (ℛ.ker_red_nilpotent _)
  have hΓ : (ℛ.redₐ (k ⊗[R] O)).comp Γ = u := Algebra.FormallySmooth.comp_liftOfSurjective _ _ _ _
  obtain ⟨χ, hχ⟩ := ℛ.classify_surjective hf Γ
  have key : ∀ ψ : ℛ.repAlg f ⟶ CommAlgCat.of κ k, ψ.hom e =
      (Algebra.TensorProduct.lift (AlgHom.id k k) ((ℛ.redₐ k).comp (ℛ.classify hf ψ))
        fun _ _ => Commute.all _ _) (χ.hom e) := by
    intro ψ
    let y : k ⊗[R] O →ₐ[k] k := Algebra.TensorProduct.lift (AlgHom.id k k)
      ((ℛ.redₐ k).comp (ℛ.classify hf ψ)) fun _ _ => Commute.all _ _
    change ψ.hom e = (χ ≫ CommAlgCat.ofHom y).hom e
    refine ℛ.idempotent_eq_of_red_eq hf he ψ _ ?_
    rw [classify_comp, hχ]
    ext x
    change ℛ.red _ ((ℛ.classify hf ψ) x) =
      ℛ.red _ ((ℛ.functor.map (CommAlgCat.ofHom y)).hom (Γ x))
    rw [ℛ.red_map]
    have hx : ℛ.red (CommAlgCat.of κ (k ⊗[R] O)) (Γ x) = u x := DFunLike.congr_fun hΓ x
    change _ = y (ℛ.red (CommAlgCat.of κ (k ⊗[R] O)) (Γ x))
    rw [hx]
    change _ = y (1 ⊗ₜ x)
    rw [Algebra.TensorProduct.lift_tmul]
    simp only [AlgHom.id_apply, one_mul, AlgHom.comp_apply]
    rfl
  rcases hD _ (he.map χ.hom) with h | h
  · left
    intro ψ
    rw [key ψ, h, map_zero]
  · right
    intro ψ
    rw [key ψ, h, map_one]

end GreenbergRingScheme

end Fibre


section Main

variable {R : Type u} [CommRing R] [IsLocalRing R] {n : ℕ+} (ℛ : GreenbergRingScheme R n)

local notation "k" => IsLocalRing.ResidueField R
local notation "κ" => CommRingCat.of (IsLocalRing.ResidueField R)

omit [IsLocalRing R] in
/-- The special fibre algebra of a geometrically connected affine scheme has only trivial
idempotents (any field-valued fibre would do). -/
theorem tensor_idempotent {K : Type u} [Field K] [Algebra R K]
    (Z : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom Z.X.hom]
    [GeometricallyConnected Z.X.hom] (d : K ⊗[R] Lie.coordinateAlgebra Z)
    (hd : IsIdempotentElem d) : d = 0 ∨ d = 1 := by
  have : IsIso (Lie.coordinateIso Z).hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso (Lie.coordinateIso Z)).hom)
  have hg : GeometricallyConnected
      ((algSpec (CommRingCat.of R)).obj (op (Lie.coordinateAlgebra Z))).hom := by
    rw [← Over.w (Lie.coordinateIso Z).hom]
    exact (MorphismProperty.cancel_left_of_respectsIso
      (@GeometricallyConnected : MorphismProperty Scheme.{u}) _ Z.X.hom).2 inferInstance
  have hc : ConnectedSpace ↥(pullback (C := Scheme.{u})
      (Spec.map (CommRingCat.ofHom (algebraMap R (Lie.coordinateAlgebra Z))))
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))) :=
    hg.geometrically_connectedSpace _ _ _ (IsPullback.of_hasPullback _ _)
  have hc' : ConnectedSpace (PrimeSpectrum (Lie.coordinateAlgebra Z ⊗[R] K)) :=
    (pullbackSpecIso R (Lie.coordinateAlgebra Z) K).hom.homeomorph.connectedSpace_iff.1 hc
  rcases eq_zero_or_one_of_connectedSpace
      (hd.map (Algebra.TensorProduct.comm R K (Lie.coordinateAlgebra Z))) with h | h
  · left
    apply (Algebra.TensorProduct.comm R K (Lie.coordinateAlgebra Z)).injective
    rw [h, map_zero]
  · right
    apply (Algebra.TensorProduct.comm R K (Lie.coordinateAlgebra Z)).injective
    rw [h, map_one]

variable [IsAlgClosed (IsLocalRing.ResidueField R)]

/-- **Connectedness.** The Greenberg group of a smooth affine group with geometrically
connected fibres is connected. -/
theorem connectedSpace_greenbergGroup (Z : GroupScheme (Spec (CommRingCat.of R)))
    [IsAffineHom Z.X.hom] (hZ : Smooth Z.X.hom) [GeometricallyConnected Z.X.hom]
    (Q : CoordPres Z) : ConnectedSpace (greenbergGroup ℛ Z Q).X.left := by
  have := smooth_coordinateAlgebra Z hZ
  change ConnectedSpace (PrimeSpectrum (ℛ.Poly Q.N ⧸ ℛ.repIdeal Q.f))
  obtain ⟨χ0, -⟩ := ℛ.classify_surjective Q.surj
    ((Algebra.ofId R (ℛ.functor.obj (CommAlgCat.of κ k))).comp (Lie.coordinateOrigin Z))
  have : Nontrivial (ℛ.Poly Q.N ⧸ ℛ.repIdeal Q.f) :=
    RingHom.domain_nontrivial χ0.hom.toRingHom
  apply connectedSpace_of_idempotents
  intro e he
  have hnil : ∀ x : ℛ.Poly Q.N ⧸ ℛ.repIdeal Q.f, IsIdempotentElem x →
      (∀ ψ : ℛ.repAlg Q.f ⟶ CommAlgCat.of κ k, ψ.hom x = 0) → x = 0 := by
    intro x hx hψ
    have hψ' : ∀ ψ : (ℛ.Poly Q.N ⧸ ℛ.repIdeal Q.f) →ₐ[k] k, ψ x = 0 := fun ψ =>
      hψ (CommAlgCat.ofHom ψ)
    obtain ⟨m, hm⟩ := isNilpotent_of_forall_algHom (ℛ.repIdeal Q.f) x hψ'
    rw [← hx.pow_succ_eq m, pow_succ, hm, zero_mul]
  rcases ℛ.idempotent_const Q.surj (tensor_idempotent Z) he with h | h
  · exact Or.inl (hnil e he h)
  · right
    have h1 := hnil (1 - e) he.one_sub fun ψ => by rw [map_sub, map_one, h ψ, sub_self]
    rw [sub_eq_zero] at h1
    exact h1.symm

/-- **Geometric connectedness.** The Greenberg group of a smooth affine group with
geometrically connected fibres is geometrically connected. -/
theorem geometricallyConnected_greenbergGroup (Z : GroupScheme (Spec (CommRingCat.of R)))
    [IsAffineHom Z.X.hom] (hZ : Smooth Z.X.hom) [GeometricallyConnected Z.X.hom]
    (Q : CoordPres Z) : GeometricallyConnected (greenbergGroup ℛ Z Q).X.hom := by
  have : Smooth (greenbergGroup ℛ Z Q).X.hom := smooth_greenbergGroup ℛ Z Q hZ
  have : ConnectedSpace (greenbergGroup ℛ Z Q).X.left :=
    connectedSpace_greenbergGroup ℛ Z hZ Q
  exact (greenbergGroup ℛ Z Q).geometricallyConnected_of_connected

end Main

end Langlands.GroupScheme.IntegralModel.GreenbergMixed
