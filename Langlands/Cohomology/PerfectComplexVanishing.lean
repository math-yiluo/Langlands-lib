import Langlands.Cohomology.FibreDimension

/-! # Vanishing of fibre homology from vanishing of homology (Mumford's Corollary 3) -/

universe u

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace Langlands.Cohomology.FibreDimension

variable {R : Type u} [CommRing R]

/-- Fibre dimensions are invariant under linear equivalences. -/
lemma fibreDim_congr {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (p : PrimeSpectrum R) : fibreDim M p = fibreDim N p :=
  (e.baseChange R p.asIdeal.ResidueField _ _).finrank_eq

/-- If `M ⧸ N` is projective, then `M ≃ N × (M ⧸ N)` compatibly with the inclusion and
the projection. -/
lemma exists_splitEquiv {M : Type u} [AddCommGroup M] [Module R M] (N : Submodule R M)
    [Module.Projective R (M ⧸ N)] :
    ∃ e : M ≃ₗ[R] N × (M ⧸ N), N.subtype = e.symm ∘ₗ LinearMap.inl R N (M ⧸ N) ∧
      N.mkQ = LinearMap.snd R N (M ⧸ N) ∘ₗ e := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.mkQ (LinearMap.id) N.mkQ_surjective
  have hex : Function.Exact N.subtype N.mkQ := LinearMap.exact_subtype_mkQ N
  obtain ⟨e, he⟩ := (hex.splitSurjectiveEquiv N.injective_subtype) ⟨s, hs⟩
  exact ⟨e, he⟩

/-- A submodule with projective quotient of a projective module is projective. -/
lemma projective_of_projective_quotient {M : Type u} [AddCommGroup M] [Module R M]
    [Module.Projective R M] (N : Submodule R M) [Module.Projective R (M ⧸ N)] :
    Module.Projective R N := by
  obtain ⟨e, he₁, -⟩ := exists_splitEquiv N
  refine Module.Projective.of_split N.subtype (LinearMap.fst R N (M ⧸ N) ∘ₗ e.toLinearMap) ?_
  refine LinearMap.ext fun x => ?_
  have : e (N.subtype x) = (x, 0) := by
    rw [he₁]
    simp
  simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearEquiv.coe_coe, this,
    LinearMap.fst_apply]

/-- Fibre dimensions are additive along a submodule with projective quotient. -/
lemma fibreDim_eq_add_of_projective_quotient {M : Type u} [AddCommGroup M] [Module R M]
    [Module.Finite R M] (N : Submodule R M) [Module.Projective R (M ⧸ N)] (p : PrimeSpectrum R) :
    fibreDim M p = fibreDim N p + fibreDim (M ⧸ N) p := by
  obtain ⟨e, -, -⟩ := exists_splitEquiv N
  have : Module.Finite R N := Module.Finite.of_surjective
    (LinearMap.fst R N (M ⧸ N) ∘ₗ e.toLinearMap)
    (fun x => ⟨e.symm (x, 0), by simp⟩)
  rw [fibreDim_congr e p]
  unfold fibreDim
  rw [(TensorProduct.prodRight R _ p.asIdeal.ResidueField N (M ⧸ N)).finrank_eq,
    Module.finrank_prod]

section Complex

variable (K : CochainComplex (ModuleCat.{u} R) ℤ)

/-- Zero homology in degree `i` is exactness: `im d^{j} = ker dⁱ` for `j + 1 = i`, `i + 1 = k`. -/
lemma range_eq_ker_of_isZero_homology {j i k : ℤ} (hj : j + 1 = i) (hk : i + 1 = k)
    (h : IsZero (K.homology i)) :
    LinearMap.range (K.d j i).hom = LinearMap.ker (K.d i k).hom := by
  subst hj hk
  have hex : K.ExactAt (j + 1) := (K.exactAt_iff_isZero_homology (j + 1)).2 h
  rw [HomologicalComplex.exactAt_iff' K j (j + 1) (j + 1 + 1) (by simp) (by simp)] at hex
  exact (ShortComplex.moduleCat_exact_iff_range_eq_ker _).1 hex

/-- With zero homology in degree `i`, the cokernel of `d^{i-1}` is the image of `dⁱ`. -/
noncomputable def cokerEquivRange {j i k : ℤ} (hj : j + 1 = i) (hk : i + 1 = k)
    (h : IsZero (K.homology i)) :
    (K.X i ⧸ LinearMap.range (K.d j i).hom) ≃ₗ[R] LinearMap.range (K.d i k).hom :=
  (Submodule.quotEquivOfEq _ _ (range_eq_ker_of_isZero_homology K hj hk h)).trans
    (LinearMap.quotKerEquivRange _)

lemma projective_coker_congr {i i' k : ℤ} (h : i = i') :
    Module.Projective R (K.X k ⧸ LinearMap.range (K.d i k).hom) ↔
      Module.Projective R (K.X k ⧸ LinearMap.range (K.d i' k).hom) := by
  subst h
  rfl

/-- One step of the descending induction: if the cokernel of `dⁱ` is projective and `Hⁱ = 0`,
the cokernel of `d^{i-1}` is projective. -/
lemma projective_coker_step {j i k : ℤ} [Module.Projective R (K.X k)] (hj : j + 1 = i)
    (hk : i + 1 = k) (h : IsZero (K.homology i))
    [Module.Projective R (K.X k ⧸ LinearMap.range (K.d i k).hom)] :
    Module.Projective R (K.X i ⧸ LinearMap.range (K.d j i).hom) := by
  have := projective_of_projective_quotient (LinearMap.range (K.d i k).hom)
  exact Module.Projective.of_equiv' (cokerEquivRange K hj hk h).symm

/-- **Cokernels are projective.** Let `K` have projective terms, vanish above `b`, and have no
homology in positive degrees. Then the cokernel of `dʲ : Kʲ → K^{j+1}` is projective for every
`j ≥ 0`. -/
theorem projective_coker [∀ i, Module.Projective R (K.X i)] {b : ℤ}
    (hb : ∀ n, b < n → IsZero (K.X n)) (hpos : ∀ i : ℤ, 0 < i → IsZero (K.homology i)) (j : ℤ)
    (hj : 0 ≤ j) : Module.Projective R (K.X (j + 1) ⧸ LinearMap.range (K.d j (j + 1)).hom) := by
  -- above `b` the cokernel is zero
  have htop : ∀ n, b ≤ n →
      Module.Projective R (K.X (n + 1) ⧸ LinearMap.range (K.d n (n + 1)).hom) := by
    intro n hn
    have : Subsingleton (K.X (n + 1)) :=
      ModuleCat.isZero_iff_subsingleton.1 (hb _ (by omega))
    infer_instance
  rcases le_or_gt b j with hbj | hbj
  · exact htop j hbj
  · have key : ∀ n ≤ b, 0 ≤ n →
        Module.Projective R (K.X (n + 1) ⧸ LinearMap.range (K.d n (n + 1)).hom) := by
      intro n hn
      induction n, hn using Int.leInductionDown with
      | base => exact fun _ => htop b le_rfl
      | pred n hn ih =>
        intro h0
        have Pn := (projective_coker_congr K (show n = n - 1 + 1 by ring)).1 (ih (by omega))
        exact projective_coker_step K (j := n - 1) (i := n - 1 + 1) (k := n + 1) rfl (by ring)
          (hpos _ (by omega))
    exact key j hbj.le hj

/-- **Mumford's Corollary 3, algebraic form.** Let `K` be a complex of finite projective modules
vanishing above some degree, with no homology in positive degrees. Then for every positive `i`
and every prime `p`, `homologyDim K i p = 0`; so `Hⁱ(K ⊗ k) = 0` for every ring map to a
field. -/
theorem homologyDim_eq_zero_of_isZero_homology [∀ i, Module.Finite R (K.X i)]
    [∀ i, Module.Projective R (K.X i)] {b : ℤ} (hb : ∀ n, b < n → IsZero (K.X n))
    (hpos : ∀ i : ℤ, 0 < i → IsZero (K.homology i)) (i : ℤ) (hi : 0 < i)
    (p : PrimeSpectrum R) : homologyDim K i p = 0 := by
  have := projective_coker K hb hpos i hi.le
  have h1 := fibreDim_congr (cokerEquivRange K (j := i - 1) (i := i) (k := i + 1) (by ring) rfl
    (hpos i hi)) p
  have h2 := fibreDim_eq_add_of_projective_quotient (LinearMap.range (K.d i (i + 1)).hom) p
  unfold homologyDim
  omega

end Complex

end Langlands.Cohomology.FibreDimension
