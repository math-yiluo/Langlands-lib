import Langlands.GroupScheme.MatrixRepresentation.GaloisCoefficients
import Langlands.Algebra.GaloisTwistedMatrix
import Langlands.GroupScheme.Rational.HighestWeightScalarEndomorphisms

/-! # The Tits algebra of a representation of a scalar-extended group -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

section BaseFunctional

variable {O : Type u} [CommRing O] [Algebra k O]

variable (K) in
/-- The `K`-linear functional `id_K ⊗ φ : K ⊗[k] O → K` of a `k`-linear functional `φ`. -/
def baseFunctional (φ : O →ₗ[k] k) : K ⊗[k] O →ₗ[K] K :=
  (Algebra.TensorProduct.rid k K K).toLinearMap ∘ₗ φ.baseChange K

@[simp] theorem baseFunctional_tmul (φ : O →ₗ[k] k) (c : K) (o : O) :
    baseFunctional K φ (c ⊗ₜ o) = φ o • c :=
  rfl

theorem baseFunctional_galoisTensor (φ : O →ₗ[k] k) (σ : K ≃ₐ[k] K) (z : K ⊗[k] O) :
    baseFunctional K φ (galoisTensor O σ z) = σ (baseFunctional K φ z) := by
  induction z with
  | tmul c o => rw [galoisTensor_tmul, baseFunctional_tmul, baseFunctional_tmul, map_smul]
  | add z w hz hw => rw [map_add, map_add, hz, hw, map_add, map_add]

/-- Finitely many elements of `K ⊗[k] O` are recovered from finitely many functionals
`id ⊗ φ_s` and vectors `1 ⊗ o_s`. -/
theorem exists_reconstruction (Z : Finset (K ⊗[k] O)) :
    ∃ (r : ℕ) (φ : Fin r → O →ₗ[k] k) (o : Fin r → O),
      ∀ z ∈ Z, z = ∑ s, baseFunctional K (φ s) z • ((1 : K) ⊗ₜ[k] o s) := by
  classical
  have hfin : ∀ z : K ⊗[k] O, ∃ T : Finset O,
      z ∈ Submodule.span K ((fun o => (1 : K) ⊗ₜ[k] o) '' (T : Set O)) := by
    intro z
    induction z with
    | tmul c o =>
      refine ⟨{o}, ?_⟩
      have : c ⊗ₜ[k] o = c • ((1 : K) ⊗ₜ[k] o) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this]
      exact Submodule.smul_mem _ c (Submodule.subset_span ⟨o, by simp, rfl⟩)
    | add z w hz hw =>
      obtain ⟨T, hT⟩ := hz
      obtain ⟨T', hT'⟩ := hw
      refine ⟨T ∪ T', Submodule.add_mem _ ?_ ?_⟩
      · exact Submodule.span_mono (Set.image_mono (by simp)) hT
      · exact Submodule.span_mono (Set.image_mono (by simp)) hT'
  choose T hT using hfin
  let F : Submodule k O := Submodule.span k (Z.biUnion T : Set O)
  let b := Module.finBasis k F
  have hext : ∀ s : Fin (Module.finrank k F), ∃ φ : O →ₗ[k] k,
      φ.comp F.subtype = b.coord s := fun s => LinearMap.exists_extend (b.coord s)
  choose φ hφ using hext
  refine ⟨Module.finrank k F, φ, fun s => (b s : O), fun z hz => ?_⟩
  have hgen : ∀ w ∈ Submodule.span K ((fun o => (1 : K) ⊗ₜ[k] o) '' (T z : Set O)),
      w = ∑ s, baseFunctional K (φ s) w • ((1 : K) ⊗ₜ[k] (b s : O)) := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨o, ho, rfl⟩ := hw
      have hoF : o ∈ F := Submodule.subset_span (Finset.mem_biUnion.mpr ⟨z, hz, ho⟩)
      have hrepr : (⟨o, hoF⟩ : F) = ∑ s, b.coord s ⟨o, hoF⟩ • b s := by
        conv_lhs => rw [← b.sum_repr ⟨o, hoF⟩]
        rfl
      have hφo : ∀ s, φ s o = b.coord s ⟨o, hoF⟩ := fun s => by
        rw [← hφ s]
        rfl
      simp only [baseFunctional_tmul, hφo]
      conv_lhs => rw [show o = ((⟨o, hoF⟩ : F) : O) from rfl, hrepr]
      rw [Submodule.coe_sum, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Submodule.coe_smul, TensorProduct.tmul_smul, smul_assoc, one_smul]
    | zero => simp
    | add w w' _ _ hw hw' =>
      simp only [map_add, add_smul, Finset.sum_add_distrib]
      rw [← hw, ← hw']
    | smul c w _ hw =>
      simp only [map_smul, smul_eq_mul, mul_smul]
      rw [← Finset.smul_sum, ← hw]
  exact hgen z (hT z)

end BaseFunctional

section Density

variable {F : Type u} [Field F] {H : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom H.X.hom]

/-- An irreducible representation whose self-intertwiners are scalars has the full
endomorphism algebra as its operator algebra (Jacobson density). -/
theorem operatorAlgebra_eq_top (ρ : MatrixRepresentation H n) (hirr : ρ.IsIrreducible)
    (hscalar : ∀ C : Matrix n n F, ρ.Intertwines ρ C → ∃ c : F, C = Matrix.scalar n c) :
    AffineCoefficientAlgebra.operatorAlgebra ρ = ⊤ := by
  let R := AffineCoefficientAlgebra.operatorAlgebra ρ
  have := AffineCoefficientAlgebra.isSimpleModule ρ hirr
  have hsmul : ∀ (c : F) (v : n → F), (algebraMap F R c) • v = c • v := fun c v => rfl
  have hend : ∀ g : Module.End R (n → F), ∃ c : F, ∀ v, g v = c • v := by
    intro g
    let gF : (n → F) →ₗ[F] (n → F) :=
      { toFun := g
        map_add' := g.map_add
        map_smul' := fun c v => by
          rw [← hsmul, g.map_smul, hsmul]
          rfl }
    let C := LinearMap.toMatrix' gF
    have hC : ρ.Intertwines ρ C := by
      rw [AffineCoefficientAlgebra.intertwines_iff]
      intro ℓ
      apply Matrix.toLin'.injective
      rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
      apply LinearMap.ext
      intro v
      have hmem : (AffineCoefficients.coefficientMap ρ ℓ).mulVecLin ∈ R :=
        Algebra.subset_adjoin ⟨ℓ, rfl⟩
      have := g.map_smul ⟨_, hmem⟩ v
      exact this
    obtain ⟨c, hc⟩ := hscalar C hC
    refine ⟨c, fun v => ?_⟩
    have h1 : gF v = C *ᵥ v := (LinearMap.toMatrix'_mulVec gF v).symm
    rw [hc, Matrix.scalar_apply] at h1
    change gF v = c • v
    rw [h1]
    funext i
    simp [Matrix.mulVec_diagonal]
  classical
  rw [eq_top_iff]
  intro T _
  obtain ⟨r, hr⟩ := jacobson_density (R := R) (M := n → F)
    { toFun := T
      map_add' := T.map_add
      map_smul' := fun g v => by
        obtain ⟨c, hc⟩ := hend g
        change T (g v) = g (T v)
        rw [hc, hc, T.map_smul] }
    (Finset.univ.image fun i => Pi.single i (1 : F))
  have hT : T = (r : Module.End F (n → F)) := by
    apply LinearMap.pi_ext'
    intro i
    apply LinearMap.ext_ring
    have := hr (Pi.single i 1) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    exact this
  rw [hT]
  exact r.2

end Density

section Tits

variable [IsAffineHom G.X.hom]

local instance titsBaseChangeAffine :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

/-- The coefficient matrix `(id_K ⊗ φ)(universalMatrix ρ)` of a `k`-linear functional `φ` on
`O(G)`. -/
def coefficientMatrix
    (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n)
    (φ : CharacterUnits.Coord G →ₗ[k] k) : Matrix n n K :=
  (universalMatrix ρ).map (baseFunctional K φ)

/-- The Tits algebra of `ρ`: the `k`-subalgebra of `M_n(K)` generated by the coefficient
matrices of `k`-linear functionals on `O(G)`. -/
def titsAlgebra
    (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n) :
    Subalgebra k (Matrix n n K) :=
  Algebra.adjoin k (Set.range (coefficientMatrix ρ))

theorem coefficientMatrix_galoisTwist (σ : K ≃ₐ[k] K)
    (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n)
    (φ : CharacterUnits.Coord G →ₗ[k] k) :
    coefficientMatrix (galoisTwist σ ρ) φ = (coefficientMatrix ρ φ).map σ := by
  rw [coefficientMatrix, coefficientMatrix, universalMatrix_galoisTwist]
  ext i j
  exact baseFunctional_galoisTensor φ σ _

/-- An intertwiner from `ρ` to its twist conjugates every coefficient matrix by `σ`. -/
theorem coefficientMatrix_intertwines (σ : K ≃ₐ[k] K)
    {ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n}
    {P : Matrix n n K} (hP : ρ.Intertwines (galoisTwist σ ρ) P)
    (φ : CharacterUnits.Coord G →ₗ[k] k) :
    P * coefficientMatrix ρ φ = (coefficientMatrix ρ φ).map σ * P := by
  rw [intertwines_iff_universalMatrix] at hP
  have h := congrArg (fun M => M.map (baseFunctional K φ)) hP
  simp only at h
  rw [AffineCoefficientAlgebra.map_mul_left, AffineCoefficientAlgebra.map_mul_right] at h
  rw [← coefficientMatrix_galoisTwist]
  exact h

/-- The Tits algebra is fixed by the twisted Galois action of intertwiners `ρ → ρ^σ`. -/
theorem titsAlgebra_le_twistedFixed
    {ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n}
    (P : (K ≃ₐ[k] K) → Matrix n n K) (hP : ∀ σ, ρ.Intertwines (galoisTwist σ ρ) (P σ)) :
    titsAlgebra ρ ≤ Algebra.GaloisTwistedMatrix.twistedFixed P := by
  rw [titsAlgebra, Algebra.adjoin_le_iff]
  rintro _ ⟨φ, rfl⟩ σ
  exact coefficientMatrix_intertwines σ (hP σ) φ

/-- Every `K`-linear coefficient of the universal matrix is a `K`-combination of coefficient
matrices of `k`-linear functionals. -/
theorem map_mem_span_coefficientMatrix
    (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n)
    (L : K ⊗[k] CharacterUnits.Coord G →ₗ[K] K) :
    (universalMatrix ρ).map L ∈ Submodule.span K (Set.range (coefficientMatrix ρ)) := by
  classical
  obtain ⟨r, φ, o, h⟩ := exists_reconstruction (K := K)
    (Finset.univ.image (fun p : n × n => universalMatrix ρ p.1 p.2))
  have hsum : (universalMatrix ρ).map L =
      ∑ s, L ((1 : K) ⊗ₜ[k] o s) • coefficientMatrix ρ (φ s) := by
    ext i j
    have hij := h (universalMatrix ρ i j) (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩)
    rw [Matrix.map_apply]
    conv_lhs => rw [hij]
    rw [map_sum, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_smul, Matrix.smul_apply, coefficientMatrix, Matrix.map_apply, smul_eq_mul,
      smul_eq_mul, mul_comm]
  rw [hsum]
  exact Submodule.sum_mem _ fun s _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨φ s, rfl⟩)

/-- The published universal coefficient matrices of `ρ`, over the coordinate algebra of `G_K`,
are `K`-combinations of coefficient matrices of `k`-linear functionals. -/
theorem coefficientMap_mem_span
    (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n)
    (ℓ : CharacterUnits.Coord ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) →ₗ[K] K) :
    AffineCoefficients.coefficientMap ρ ℓ ∈
      Submodule.span K (Set.range (coefficientMatrix ρ)) := by
  let A := CharacterUnits.Coord ((GroupScheme.baseChange (algebraBaseMap k K)).obj G)
  let : Algebra k A := Algebra.compHom A (algebraMap k K)
  have : IsScalarTower k K A := IsScalarTower.of_algebraMap_eq' rfl
  have h := affineMatrix_eq_map_universalEval (A := A) ρ (CharacterUnits.universalPoint _)
  have hc : AffineCoefficients.coefficientMap ρ ℓ = (universalMatrix ρ).map
      (ℓ.comp (universalEval (A := A) (CharacterUnits.universalPoint _)).toLinearMap) := by
    have h' : (ρ.affineMatrix (CharacterUnits.Coord _) (CharacterUnits.universalPoint _) :
        Matrix n n A) = (universalMatrix ρ).map
          (universalEval (A := A) (CharacterUnits.universalPoint _)) := h
    change ρ.universalCharacterMatrix.map ℓ = _
    rw [universalCharacterMatrix, h', Matrix.map_map]
    rfl
  rw [hc]
  exact map_mem_span_coefficientMatrix ρ _

/-- The `K`-span of the Tits algebra of an irreducible representation with scalar
self-intertwiners is all of `M_n(K)`. -/
theorem span_titsAlgebra_eq_top
    (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n)
    (hirr : ρ.IsIrreducible)
    (hscalar : ∀ C : Matrix n n K, ρ.Intertwines ρ C → ∃ c : K, C = Matrix.scalar n c) :
    Submodule.span K (titsAlgebra ρ : Set (Matrix n n K)) = ⊤ := by
  let S := Submodule.span K (titsAlgebra ρ : Set (Matrix n n K))
  have hmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S := by
    intro x hx y hy
    induction hx using Submodule.span_induction with
    | mem x hx =>
      induction hy using Submodule.span_induction with
      | mem y hy => exact Submodule.subset_span ((titsAlgebra ρ).mul_mem hx hy)
      | zero => simp
      | add y w _ _ h1 h2 => rw [mul_add]; exact S.add_mem h1 h2
      | smul c y _ h1 => rw [Matrix.mul_smul]; exact S.smul_mem c h1
    | zero => simp
    | add x w _ _ h1 h2 => rw [add_mul]; exact S.add_mem h1 h2
    | smul c x _ h1 => rw [Matrix.smul_mul]; exact S.smul_mem c h1
  let S' : Subalgebra K (Matrix n n K) :=
    { carrier := S
      mul_mem' := fun hx hy => hmul _ hx _ hy
      add_mem' := fun hx hy => S.add_mem hx hy
      algebraMap_mem' := fun c => by
        rw [Algebra.algebraMap_eq_smul_one]
        exact S.smul_mem c (Submodule.subset_span (titsAlgebra ρ).one_mem) }
  have hgen : Set.range (coefficientMatrix ρ) ⊆ (titsAlgebra ρ : Set (Matrix n n K)) :=
    Algebra.subset_adjoin
  have hle : AffineCoefficientAlgebra.operatorAlgebra ρ ≤
      S'.map (Matrix.toLinAlgEquiv' : Matrix n n K ≃ₐ[K] Module.End K (n → K)).toAlgHom := by
    rw [AffineCoefficientAlgebra.operatorAlgebra, Algebra.adjoin_le_iff]
    rintro _ ⟨ℓ, rfl⟩
    exact ⟨AffineCoefficients.coefficientMap ρ ℓ,
      Submodule.span_mono hgen (coefficientMap_mem_span ρ ℓ), rfl⟩
  have htop := operatorAlgebra_eq_top ρ hirr hscalar
  rw [eq_top_iff]
  intro X _
  have hX : X.mulVecLin ∈ AffineCoefficientAlgebra.operatorAlgebra ρ := by
    rw [htop]
    exact Algebra.mem_top
  obtain ⟨Y, hY, hYX⟩ := hle hX
  have hYeq : Y = X := Matrix.toLin'.injective hYX
  rw [← hYeq]
  exact hY

end Tits

section CentralSimple

variable [IsAffineHom G.X.hom] [IsGalois k K] [Nonempty n]

/-- The Tits algebra of an irreducible representation with scalar self-intertwiners which is
isomorphic to all its Galois twists, as a central simple algebra over `k`. -/
def titsCSA
    (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n)
    (hirr : ρ.IsIrreducible)
    (hscalar : ∀ C : Matrix n n K, ρ.Intertwines ρ C → ∃ c : K, C = Matrix.scalar n c)
    (P : (K ≃ₐ[k] K) → Matrix n n K) (hPunit : ∀ σ, IsUnit (P σ))
    (hP : ∀ σ, ρ.Intertwines (galoisTwist σ ρ) (P σ)) : CSA.{u, u} k :=
  Algebra.GaloisTwistedMatrix.toCSA P hPunit (titsAlgebra ρ) (titsAlgebra_le_twistedFixed P hP)
    (span_titsAlgebra_eq_top ρ hirr hscalar)

theorem titsCSA_carrier
    (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n)
    (hirr : ρ.IsIrreducible)
    (hscalar : ∀ C : Matrix n n K, ρ.Intertwines ρ C → ∃ c : K, C = Matrix.scalar n c)
    (P : (K ≃ₐ[k] K) → Matrix n n K) (hPunit : ∀ σ, IsUnit (P σ))
    (hP : ∀ σ, ρ.Intertwines (galoisTwist σ ρ) (P σ)) :
    (titsCSA ρ hirr hscalar P hPunit hP : Type u) = titsAlgebra ρ :=
  rfl

omit [Nonempty n] in
/-- The Tits algebra has dimension `n²` over `k`. -/
theorem finrank_titsAlgebra
    (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n)
    (hirr : ρ.IsIrreducible)
    (hscalar : ∀ C : Matrix n n K, ρ.Intertwines ρ C → ∃ c : K, C = Matrix.scalar n c)
    (P : (K ≃ₐ[k] K) → Matrix n n K) (hPunit : ∀ σ, IsUnit (P σ))
    (hP : ∀ σ, ρ.Intertwines (galoisTwist σ ρ) (P σ)) :
    Module.finrank k (titsAlgebra ρ) = Fintype.card n * Fintype.card n :=
  Algebra.GaloisTwistedMatrix.finrank_eq P hPunit (titsAlgebra ρ)
    (titsAlgebra_le_twistedFixed P hP) (span_titsAlgebra_eq_top ρ hirr hscalar)

end CentralSimple

end Langlands.GroupScheme.MatrixRepresentation
