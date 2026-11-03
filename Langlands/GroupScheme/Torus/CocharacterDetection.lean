import Langlands.GroupScheme.Torus.CocharacterSplitting
import Langlands.GroupScheme.Torus.CocharacterInseparableDescent
import Langlands.GroupScheme.Torus.CocharacterGaloisDescent
import Langlands.GroupScheme.Rational.SplitComponentProof
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.RingTheory.Jacobson.Ring

/-! # Cocharacters detecting the characters of a torus

A nonzero rational character of a torus `Z` over a field `k` restricts nontrivially to some
homomorphism `𝔾_m ⟶ Z`. A splitting field `K` gives a cocharacter datum over `K[ℤ]`; it descends to
a finitely generated subalgebra of `K`, then to a residue field `L` of it, finite over `k`, then
to the separable closure of `k` in `L`, and finally, by Galois descent, to `k` itself.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.CocharacterDatum

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] {Z : CommGroupScheme (Spec (CommRingCat.of k))}
variable {Λ : Type u} [AddCommGroup Λ]

/-- **Frobenius on points of a torus.** If a `k`-algebra map `g : A → A` agrees with the identity
after taking `p ^ e`-th powers, `p` the exponential characteristic of `k`, then so does its action
on the points of a torus. -/
theorem pow_affineMap_eq_of_isTorus [IsAffine Z.toGrp.X.left] (hZ : IsTorus Z.toGrp) (p e : ℕ) [ExpChar k p]
    (A : Type u) [CommRing A] [Algebra k A] (g : A →ₐ[k] A) (hg : ∀ a, a ^ p ^ e = g a ^ p ^ e)
    (x : Lie.AffinePoints Z.toGrp A) : x ^ p ^ e = Lie.affineMap Z.toGrp g x ^ p ^ e := by
  obtain ⟨K, _, _, I, _, ⟨s⟩⟩ := hZ
  exact CocharacterSplitting.pow_affineMap_eq_of_tensor s (p ^ e) g
    (CocharacterDescent.pow_eq_pow_tensorProductMap p e g hg) x

/-- **Descent to a finitely generated subalgebra.** A cocharacter datum over `K[Λ]`, `K` a field
over `k`, comes from a datum of the same weight over `B[Λ]` for a finitely generated
`k`-subalgebra `B` of `K`, provided the coordinate algebra of `Z` is of finite type. -/
theorem IsDatum.exists_finiteType [IsAffine Z.toGrp.X.left]
    (hfin : Algebra.FiniteType (CommRingCat.of k) (coordAlgebra Z.toGrp))
    {K : Type u} [Field K] [Algebra k K] {χ : characterLattice Z} {m : Λ}
    {x : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra K Λ)} (hx : IsDatum χ m x) :
    ∃ B : Subalgebra k K, Algebra.FiniteType k B ∧
      ∃ y : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra B Λ), IsDatum χ m y := by
  classical
  obtain ⟨s, hs⟩ := hfin.out
  let T : Finset K := s.biUnion fun c => ((coord x).hom c).coeff.frange
  let B : Subalgebra k K := Algebra.adjoin k (T : Set K)
  refine ⟨B, Algebra.FiniteType.adjoin_of_finite T.finite_toSet, ?_⟩
  have hgen : ∀ c ∈ s, (coord x).hom c ∈ (AddMonoidAlgebra.mapAlgHom Λ B.val).range := by
    intro c hc
    obtain ⟨y, hy⟩ := exists_mapAlgHom_eq B.val Subtype.val_injective ((coord x).hom c)
      fun γ => by
        by_cases h : ((coord x).hom c).coeff γ = 0
        · rw [h]
          exact zero_mem _
        · refine (AlgHom.mem_range _).mpr ⟨⟨_, Algebra.subset_adjoin ?_⟩, rfl⟩
          exact Finset.mem_biUnion.mpr ⟨c, hc, Finsupp.mem_frange.mpr ⟨h, γ, rfl⟩⟩
    exact ⟨y, hy⟩
  have hall : ∀ c, (coord x).hom c ∈ (AddMonoidAlgebra.mapAlgHom Λ B.val).range := by
    intro c
    have hc : c ∈ Algebra.adjoin (CommRingCat.of k) (s : Set (coordAlgebra Z.toGrp)) := by
      rw [hs]
      trivial
    induction hc using Algebra.adjoin_induction with
    | mem c hc => exact hgen c hc
    | algebraMap r =>
      rw [AlgHom.commutes]
      exact Subalgebra.algebraMap_mem _ (r : k)
    | add a b _ _ ha hb =>
      rw [map_add]
      exact add_mem ha hb
    | mul a b _ _ ha hb =>
      rw [map_mul]
      exact mul_mem ha hb
  obtain ⟨y, hy⟩ := exists_affineMap_eq _ (mapAlgHom_injective B.val Subtype.val_injective) x hall
  refine ⟨y, IsDatum.of_coeff_map B.val Subtype.val_injective ?_⟩
  change IsDatum χ m (Lie.affineMap Z.toGrp _ y)
  rw [hy]
  exact hx

/-- **Specialization to a finite extension.** A cocharacter datum over `B[Λ]`, `B` a nonzero
finitely generated `k`-algebra, gives one of the same weight over `L[Λ]` for a field `L` finite
over `k`: a residue field of `B` at a maximal ideal (Zariski's lemma). -/
theorem IsDatum.exists_finiteDimensional {B : Type u} [CommRing B] [Algebra k B] [Nontrivial B]
    [Algebra.FiniteType k B] {χ : characterLattice Z} {m : Λ}
    {y : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra B Λ)} (hy : IsDatum χ m y) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L), FiniteDimensional k L ∧
      ∃ z : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra L Λ), IsDatum χ m z := by
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal B
  let := Ideal.Quotient.field 𝔪
  have : Algebra.FiniteType k (B ⧸ 𝔪) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k 𝔪) (Ideal.Quotient.mkₐ_surjective k 𝔪)
  exact ⟨B ⧸ 𝔪, inferInstance, inferInstance, finite_of_finite_type_of_isJacobsonRing k (B ⧸ 𝔪),
    _, hy.coeff_map (Ideal.Quotient.mkₐ k 𝔪)⟩

/-- **Descent to the separable closure.** On a torus, a cocharacter datum over `L[Λ]`, `L` finite
over `k`, comes from a datum of the same weight over the separable closure of `k` in `L`. -/
theorem IsDatum.exists_separableClosure [IsAffine Z.toGrp.X.left] [IsAddTorsionFree Λ]
    (hZ : IsTorus Z.toGrp) {L : Type u} [Field L] [Algebra k L] [FiniteDimensional k L]
    {χ : characterLattice Z} {m : Λ} {z : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra L Λ)}
    (hz : IsDatum χ m z) :
    ∃ w : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra (separableClosure k L) Λ), IsDatum χ m w := by
  obtain ⟨p, _⟩ := ExpChar.exists k
  have : ExpChar (separableClosure k L) p :=
    expChar_of_injective_algebraMap (algebraMap k (separableClosure k L)).injective p
  have : FiniteDimensional (separableClosure k L) L :=
    Module.Finite.of_restrictScalars_finite k (separableClosure k L) L
  exact IsDatum.exists_of_pow_mem_range p (IsPurelyInseparable.exponent (separableClosure k L) L)
    (fun A _ _ g hg x => pow_affineMap_eq_of_isTorus hZ p _ A g hg x)
    (fun ℓ => IsPurelyInseparable.exponent_def' (separableClosure k L) p ℓ) hz

/-- **Descent from a finite separable extension.** A cocharacter datum of weight `m` over `F[Λ]`,
`F` finite and separable over `k`, gives a datum over `k[Λ]` of weight `n • m` for some `n ≠ 0`:
move it into the normal closure of `F` in a separable closure of `k`, which is finite Galois over
`k`, and take the product of its Galois conjugates. -/
theorem IsDatum.exists_of_isSeparable [IsAffine Z.toGrp.X.left] {F : Type u} [Field F]
    [Algebra k F] [FiniteDimensional k F] [Algebra.IsSeparable k F] {χ : characterLattice Z}
    {m : Λ} {w : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra F Λ)} (hw : IsDatum χ m w) :
    ∃ n : ℕ, n ≠ 0 ∧ ∃ v : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra k Λ), IsDatum χ (n • m) v := by
  let N := IntermediateField.normalClosure k F (SeparableClosure k)
  have : IsGalois k N :=
    { to_isSeparable := Algebra.isSeparable_tower_bot_of_isSeparable k N (SeparableClosure k)
      to_normal := inferInstance }
  let g : F →ₐ[k] N := (normalClosure.algHomEquiv k F (SeparableClosure k)).symm IsSepClosed.lift
  obtain ⟨v, hv⟩ := (hw.coeff_map g).exists_of_isGalois
  exact ⟨_, Nat.card_pos.ne', v, hv⟩

end Langlands.GroupScheme.CocharacterDatum

namespace Langlands.GroupScheme.CocharacterDetection

set_option backward.isDefEq.respectTransparency false

open CocharacterDatum

variable {k : Type u} [Field k] {Z : CommGroupScheme (Spec (CommRingCat.of k))}

/-- **Cocharacters detect characters of tori.** A nonzero rational character `χ` of a torus `Z`
over a field `k`, affine and locally of finite type over `k`, restricts nontrivially to some
homomorphism `𝔾_m ⟶ Z`. -/
theorem exists_gm_characterRestrict_ne_zero_of_isTorus [IsAffineHom Z.toGrp.X.hom]
    [LocallyOfFiniteType Z.toGrp.X.hom] (hZ : IsTorus Z.toGrp) {χ : rationalCharacters Z.toGrp}
    (hχ : χ ≠ 0) : ∃ φ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ Z.toGrp, characterRestrict φ χ ≠ 0 := by
  have : IsAffine Z.toGrp.X.left := isAffine_of_isAffineHom Z.toGrp.X.hom
  obtain ⟨K, _, _, I, _, ⟨s⟩⟩ := id hZ
  have := Fintype.ofFinite I
  obtain ⟨m, x, hm, hx⟩ := CocharacterSplitting.exists_isDatum s hχ
  obtain ⟨B, _, y, hy⟩ := hx.exists_finiteType (finiteType_coordinateAlgebra Z.toGrp)
  obtain ⟨L, _, _, _, z, hz⟩ := hy.exists_finiteDimensional
  obtain ⟨w, hw⟩ := hz.exists_separableClosure hZ
  obtain ⟨n, hn, v, hv⟩ := hw.exists_of_isSeparable
  exact CocharacterDatum.exists_gm_characterRestrict_ne_zero
    (fun h => hm ((nsmul_eq_zero_iff_right hn).mp h)) hv

end Langlands.GroupScheme.CocharacterDetection
