import Langlands.GroupScheme.IntegralModel.GreenbergMixed.Basic
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Smooth.Basic

/-! # Corepresenting `B ↦ Hom_R(O, ℛ(B))` by a finite-type `k`-algebra

For a Greenberg ring scheme `ℛ` with `dim` coordinates and an `R`-algebra `O` with a
surjection `f : R[x_1, …, x_N] → O`, the functor `B ↦ Hom_R(O, ℛ(B))` on `k`-algebras is
corepresented by the quotient of `k[x_{m,j}]` (`m < N`, `j < dim`) by the coordinates of the
relations of `O` evaluated at the universal family of `N` points of `ℛ`.
-/

noncomputable section

universe u

open CategoryTheory

namespace Langlands.GroupScheme.IntegralModel.GreenbergMixed.GreenbergRingScheme

variable {R : Type u} [CommRing R] [IsLocalRing R] {n : ℕ+} (ℛ : GreenbergRingScheme R n)

local notation "k" => IsLocalRing.ResidueField R
local notation "κ" => CommRingCat.of (IsLocalRing.ResidueField R)

/-- The polynomial algebra on the coordinates of `N` points of `ℛ`. -/
abbrev Poly (N : ℕ) : Type u := MvPolynomial (Fin N × Fin ℛ.dim) k

/-- The universal family of `N` points of `ℛ`. -/
def univ (N : ℕ) (m : Fin N) : ℛ.functor.obj (CommAlgCat.of κ (ℛ.Poly N)) :=
  (ℛ.coord _).symm fun j => MvPolynomial.X (m, j)

/-- The family of points of `ℛ(S)` classified by an algebra map out of `ℛ.Poly N`. -/
def pointsOf {N : ℕ} {S : CommAlgCat.{u} κ} (φ : ℛ.Poly N →ₐ[k] S) (m : Fin N) :
    ℛ.functor.obj S :=
  (ℛ.functor.map (CommAlgCat.ofHom φ)).hom (ℛ.univ N m)

theorem coord_pointsOf {N : ℕ} {S : CommAlgCat.{u} κ} (φ : ℛ.Poly N →ₐ[k] S) (m : Fin N)
    (j : Fin ℛ.dim) : ℛ.coord S (ℛ.pointsOf φ m) j = φ (MvPolynomial.X (m, j)) := by
  rw [pointsOf, ℛ.coord_map, univ, Equiv.apply_symm_apply]
  rfl

theorem aeval_pointsOf {N : ℕ} {S : CommAlgCat.{u} κ} (φ : ℛ.Poly N →ₐ[k] S)
    (g : MvPolynomial (Fin N) R) :
    MvPolynomial.aeval (ℛ.pointsOf φ) g =
      (ℛ.functor.map (CommAlgCat.ofHom φ)).hom (MvPolynomial.aeval (ℛ.univ N) g) := by
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  rfl

theorem pointsOf_comp {N : ℕ} {S T : CommAlgCat.{u} κ} (φ : ℛ.Poly N →ₐ[k] S) (h : S ⟶ T)
    (m : Fin N) :
    ℛ.pointsOf (h.hom.comp φ) m = (ℛ.functor.map h).hom (ℛ.pointsOf φ m) := by
  change (ℛ.functor.map (CommAlgCat.ofHom φ ≫ h)).hom _ = _
  rw [Functor.map_comp]
  rfl

variable {O : CommAlgCat.{u} (CommRingCat.of R)} {N : ℕ}
  (f : MvPolynomial (Fin N) R →ₐ[R] O)

/-- The coordinates of the relations of `O` at the universal family of points. -/
def relations : Set (ℛ.Poly N) :=
  {q | ∃ g ∈ RingHom.ker f, ∃ j, q = ℛ.coord _ (MvPolynomial.aeval (ℛ.univ N) g) j -
    ℛ.coord _ 0 j}

/-- The ideal of the representing algebra. -/
abbrev repIdeal : Ideal (ℛ.Poly N) := Ideal.span (ℛ.relations f)

/-- The representing algebra `k[x_{m,j}] ⧸ (relations)`. -/
abbrev repAlg : CommAlgCat.{u} κ := CommAlgCat.of κ (ℛ.Poly N ⧸ ℛ.repIdeal f)

theorem aeval_pointsOf_eq_zero_iff {S : CommAlgCat.{u} κ} (φ : ℛ.Poly N →ₐ[k] S)
    (g : MvPolynomial (Fin N) R) :
    MvPolynomial.aeval (ℛ.pointsOf φ) g = 0 ↔
      ∀ j, φ (ℛ.coord _ (MvPolynomial.aeval (ℛ.univ N) g) j - ℛ.coord _ 0 j) = 0 := by
  have h0 : ∀ j, φ (ℛ.coord (CommAlgCat.of κ (ℛ.Poly N)) 0 j) = ℛ.coord S 0 j := by
    intro j
    rw [← map_zero (ℛ.functor.map (CommAlgCat.ofHom φ)).hom, ℛ.coord_map]
    rfl
  have h1 : ∀ j, φ (ℛ.coord _ (MvPolynomial.aeval (ℛ.univ N) g) j) =
      ℛ.coord S (MvPolynomial.aeval (ℛ.pointsOf φ) g) j := by
    intro j
    rw [aeval_pointsOf, ℛ.coord_map]
    rfl
  constructor
  · intro h j
    rw [map_sub, h0, h1, h, sub_self]
  · intro h
    apply ℛ.ext_coord
    intro j
    have := h j
    rw [map_sub, h0, h1, sub_eq_zero] at this
    exact this

theorem repIdeal_le_ker_iff {S : CommAlgCat.{u} κ} (φ : ℛ.Poly N →ₐ[k] S) :
    ℛ.repIdeal f ≤ RingHom.ker φ ↔
      ∀ g ∈ RingHom.ker f, MvPolynomial.aeval (ℛ.pointsOf φ) g = 0 := by
  rw [Ideal.span_le]
  constructor
  · intro h g hg
    rw [ℛ.aeval_pointsOf_eq_zero_iff]
    intro j
    exact h ⟨g, hg, j, rfl⟩
  · rintro h q ⟨g, hg, j, rfl⟩
    exact (ℛ.aeval_pointsOf_eq_zero_iff φ g).1 (h g hg) j

/-- The polynomial algebra map underlying a map out of the representing algebra. -/
abbrev polyHom {S : CommAlgCat.{u} κ} (ψ : ℛ.repAlg f ⟶ S) : ℛ.Poly N →ₐ[k] S :=
  ψ.hom.comp (Ideal.Quotient.mkₐ κ (ℛ.repIdeal f))

theorem repIdeal_le_ker_polyHom {S : CommAlgCat.{u} κ} (ψ : ℛ.repAlg f ⟶ S) :
    ℛ.repIdeal f ≤ RingHom.ker (ℛ.polyHom f ψ) := by
  intro q hq
  rw [RingHom.mem_ker]
  change ψ.hom (Ideal.Quotient.mk _ q) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.2 hq, map_zero]

variable {f} (hf : Function.Surjective f)

/-- The `R`-algebra map `O → ℛ(S)` classified by a map out of the representing algebra. -/
def classify {S : CommAlgCat.{u} κ} (ψ : ℛ.repAlg f ⟶ S) : O →ₐ[R] ℛ.functor.obj S :=
  AlgHom.liftOfSurjective f hf (MvPolynomial.aeval (ℛ.pointsOf (ℛ.polyHom f ψ))) fun g hg =>
    (ℛ.repIdeal_le_ker_iff f _).1 (ℛ.repIdeal_le_ker_polyHom f ψ) g hg

theorem classify_apply {S : CommAlgCat.{u} κ} (ψ : ℛ.repAlg f ⟶ S)
    (g : MvPolynomial (Fin N) R) :
    ℛ.classify hf ψ (f g) = MvPolynomial.aeval (ℛ.pointsOf (ℛ.polyHom f ψ)) g :=
  AlgHom.liftOfSurjective_apply _ _ _ _ _

theorem classify_comp {S T : CommAlgCat.{u} κ} (ψ : ℛ.repAlg f ⟶ S) (h : S ⟶ T) :
    ℛ.classify hf (ψ ≫ h) = (ℛ.functor.map h).hom.comp (ℛ.classify hf ψ) := by
  ext x
  obtain ⟨g, rfl⟩ := hf x
  rw [AlgHom.comp_apply, classify_apply, classify_apply]
  have hp : ℛ.pointsOf (ℛ.polyHom f (ψ ≫ h)) =
      fun m => (ℛ.functor.map h).hom (ℛ.pointsOf (ℛ.polyHom f ψ) m) := by
    funext m
    exact ℛ.pointsOf_comp (ℛ.polyHom f ψ) h m
  rw [hp, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]

theorem classify_injective {S : CommAlgCat.{u} κ} :
    Function.Injective (ℛ.classify hf (S := S)) := by
  intro ψ ψ' h
  apply CommAlgCat.hom_ext
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  rintro ⟨m, j⟩
  have key : ∀ ψ : ℛ.repAlg f ⟶ S, (ψ.hom.comp (Ideal.Quotient.mkₐ κ (ℛ.repIdeal f)))
      (MvPolynomial.X (m, j)) = ℛ.coord S (ℛ.classify hf ψ (f (MvPolynomial.X m))) j := by
    intro ψ
    rw [classify_apply, MvPolynomial.aeval_X, coord_pointsOf]
  rw [key, key, h]

theorem classify_surjective {S : CommAlgCat.{u} κ} :
    Function.Surjective (ℛ.classify hf (S := S)) := by
  intro q
  let φ : ℛ.Poly N →ₐ[k] S :=
    MvPolynomial.aeval fun i => ℛ.coord S (q (f (MvPolynomial.X i.1))) i.2
  have hpt : ℛ.pointsOf φ = fun m => q (f (MvPolynomial.X m)) := by
    funext m
    apply ℛ.ext_coord
    intro j
    rw [coord_pointsOf, MvPolynomial.aeval_X]
  have hev : ∀ g, MvPolynomial.aeval (ℛ.pointsOf φ) g = q (f g) := by
    intro g
    rw [hpt]
    exact (DFunLike.congr_fun (MvPolynomial.aeval_unique (q.comp f)) g).symm
  have hker : ℛ.repIdeal f ≤ RingHom.ker φ := by
    rw [ℛ.repIdeal_le_ker_iff]
    intro g hg
    rw [hev, RingHom.mem_ker.1 hg, map_zero]
  refine ⟨CommAlgCat.ofHom (Ideal.Quotient.liftₐ (ℛ.repIdeal f) φ hker), ?_⟩
  ext x
  obtain ⟨g, rfl⟩ := hf x
  rw [classify_apply]
  have hφ : ℛ.polyHom f (CommAlgCat.ofHom (Ideal.Quotient.liftₐ (ℛ.repIdeal f) φ hker)) = φ :=
    Ideal.Quotient.liftₐ_comp _ _ _
  rw [hφ, hev]

/-- **The corepresenting bijection** `(repAlg ⟶ S) ≃ (O ⟶ ℛ(S))`. -/
def repEquiv (S : CommAlgCat.{u} κ) : (ℛ.repAlg f ⟶ S) ≃ (O ⟶ ℛ.functor.obj S) :=
  (Equiv.ofBijective _ ⟨ℛ.classify_injective hf, ℛ.classify_surjective hf⟩).trans
    { toFun := fun g => CommAlgCat.ofHom g
      invFun := fun g => g.hom
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

@[simp] theorem repEquiv_hom {S : CommAlgCat.{u} κ} (ψ : ℛ.repAlg f ⟶ S) :
    (ℛ.repEquiv hf S ψ).hom = ℛ.classify hf ψ := rfl

theorem repEquiv_comp {S T : CommAlgCat.{u} κ} (ψ : ℛ.repAlg f ⟶ S) (h : S ⟶ T) :
    ℛ.repEquiv hf T (ψ ≫ h) = ℛ.repEquiv hf S ψ ≫ ℛ.functor.map h := by
  apply CommAlgCat.hom_ext
  exact ℛ.classify_comp hf ψ h

/-- **Corepresentability.** If `G` is corepresented by `O`, then `ℛ ⋙ G` is corepresented by
the representing algebra. -/
def corepresentableBy {G : CommAlgCat.{u} (CommRingCat.of R) ⥤ Type u}
    (e : G.CorepresentableBy O) : (ℛ.functor ⋙ G).CorepresentableBy (ℛ.repAlg f) where
  homEquiv {S} := (ℛ.repEquiv hf S).trans e.homEquiv
  homEquiv_comp {S T} h ψ := by
    change e.homEquiv (ℛ.repEquiv hf T (ψ ≫ h)) = G.map (ℛ.functor.map h)
      (e.homEquiv (ℛ.repEquiv hf S ψ))
    rw [repEquiv_comp, e.homEquiv_comp]

theorem corepresentableBy_homEquiv {G : CommAlgCat.{u} (CommRingCat.of R) ⥤ Type u}
    (e : G.CorepresentableBy O) {S : CommAlgCat.{u} κ} (ψ : ℛ.repAlg f ⟶ S) :
    (ℛ.corepresentableBy hf e).homEquiv ψ = e.homEquiv (ℛ.repEquiv hf S ψ) := rfl

/-- The representing algebra is of finite presentation over `k`. -/
theorem finitePresentation_repAlg :
    Algebra.FinitePresentation k (ℛ.Poly N ⧸ ℛ.repIdeal f) := by
  have : Algebra.FiniteType k (ℛ.Poly N ⧸ ℛ.repIdeal f) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k (ℛ.repIdeal f))
      Ideal.Quotient.mk_surjective
  exact Algebra.FinitePresentation.of_finiteType.1 this

/-- **Formal smoothness.** If `O` is formally smooth over `R`, the representing algebra is
formally smooth over `k`: lifts along square-zero thickenings of coefficients come from
lifts along the nilpotent thickenings `ℛ(C) → ℛ(C ⧸ I)`. -/
theorem formallySmooth_repAlg (hf : Function.Surjective f) [Algebra.FormallySmooth R O] :
    Algebra.FormallySmooth k (ℛ.Poly N ⧸ ℛ.repIdeal f) := by
  refine Algebra.FormallySmooth.of_comp_surjective fun C _ _ I hI g => ?_
  let C' : CommAlgCat.{u} κ := CommAlgCat.of κ C
  let π : C' ⟶ CommAlgCat.of κ (C ⧸ I) := CommAlgCat.ofHom (Ideal.Quotient.mkₐ κ I)
  let q := ℛ.classify hf (CommAlgCat.ofHom g : ℛ.repAlg f ⟶ CommAlgCat.of κ (C ⧸ I))
  let q' : O →ₐ[R] ℛ.functor.obj C' :=
    Algebra.FormallySmooth.liftOfSurjective q (ℛ.functor.map π).hom
      (ℛ.map_surjective π Ideal.Quotient.mk_surjective) (ℛ.ker_map_nilpotent C' I hI)
  obtain ⟨ψ, hψ⟩ := ℛ.classify_surjective hf q'
  refine ⟨ψ.hom, ?_⟩
  have h1 : ℛ.classify hf (ψ ≫ π) = ℛ.classify hf (CommAlgCat.ofHom g) := by
    rw [classify_comp, hψ]
    exact Algebra.FormallySmooth.comp_liftOfSurjective _ _ _ _
  have h2 := ℛ.classify_injective hf h1
  exact congrArg CommAlgCat.Hom.hom h2

end Langlands.GroupScheme.IntegralModel.GreenbergMixed.GreenbergRingScheme
