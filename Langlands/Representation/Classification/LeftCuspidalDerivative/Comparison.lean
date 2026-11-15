import Langlands.Representation.Classification.LeftCuspidalDerivative.Clause4
import Langlands.Representation.Classification.LeftCuspidalDerivative.FirstBlock
import Langlands.Representation.Filtration.NonzeroImageIrreducibleQuotient
import Langlands.Representation.Classification.JuxtaposedJacquetImage

/-!
# The comparison step: from `𝔄 × Y` to `𝔄 × E`

For a supercuspidal `A` of `GL_d`, an irreducible `A`-pure `𝔄` of `GL_a` and a left
`A`-reduced `Y` of `GL_m` (`d, a, m > 0`), every irreducible subrepresentation `π` of
`𝔄 × Y` embeds into `𝔄 × E` for some irreducible subrepresentation `E` of `Y`
(`exists_isSubrepresentation_of_isSubrepresentation_binaryProduct`).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open scoped TensorProduct

namespace Langlands.Classification.LeftCuspidalDerivative

open GeneralLinear Geometric CuspidalSupport PadicField.TopologicalData

universe uF uV uG uI uX uM uW uU

section Slots

variable {ι : Type uI} [DecidableEq ι] {H : ι → Type uG} [∀ i, Group (H i)]
  {V : ι → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  {W : ι → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
  {X : Type uX} [AddCommGroup X] [Module ℂ X]

/-- A nonzero intertwiner into the restriction of an external tensor product to the coordinate
group `H k` gives a nonzero intertwiner into the factor at `k`. -/
theorem exists_slot_ne_zero (J : ∀ i, Representation ℂ (H i) (V i)) (k : ι)
    (π : Representation ℂ (H k) X)
    (f : π.IntertwiningMap ((FiniteTensor.external J).comp (MonoidHom.mulSingle H k)))
    (hf : f ≠ 0) : ∃ g : π.IntertwiningMap (J k), g ≠ 0 := by
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (Representation.IntertwiningMap.ext (LinearMap.ext h))
  let f' : π.IntertwiningMap (FiniteTensor.action (FiniteTensor.slotRestriction J k)) := f
  let e := FiniteTensor.slotEquiv (FiniteTensor.slotRestriction J k) k
  have hex : e.toLinearEquiv (f' x) ≠ 0 := fun h0 =>
    hx (e.toLinearEquiv.injective (h0.trans (map_zero _).symm))
  obtain ⟨φ, hφ⟩ := exists_dual_lid_rTensor_ne_zero hex
  let c := FiniteTensor.trivialContraction _ (FiniteTensor.action_slotRestriction_compl J k)
    (FiniteTensor.slotRestriction J k k) φ
  let r := equivOfRepresentationEq (FiniteTensor.slotRestriction_self J k)
  refine ⟨r.toIntertwiningMap.comp (c.comp (e.toIntertwiningMap.comp f')), fun h0 => hφ ?_⟩
  exact congrArg (fun g : π.IntertwiningMap (J k) => g x) h0

/-- A nonzero intertwiner between external tensor products gives a nonzero intertwiner between
the factors at any coordinate. -/
theorem exists_slot_map_ne_zero [Fintype ι] (ρ : ∀ i, Representation ℂ (H i) (V i))
    (τ : ∀ i, Representation ℂ (H i) (W i))
    (f : (FiniteTensor.external ρ).IntertwiningMap (FiniteTensor.external τ)) (hf : f ≠ 0)
    (k : ι) : ∃ g : (ρ k).IntertwiningMap (τ k), g ≠ 0 := by
  obtain ⟨v, hv⟩ : ∃ v : ∀ i, V i, f (PiTensorProduct.tprod ℂ v) ≠ 0 := by
    by_contra h
    push Not at h
    apply hf
    apply Representation.IntertwiningMap.ext
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply, Representation.IntertwiningMap.coe_toLinearMap,
      Representation.IntertwiningMap.zero_toLinearMap, LinearMap.zero_apply]
    exact h v
  let L : V k →ₗ[ℂ] PiTensorProduct ℂ V := (PiTensorProduct.tprod ℂ).toLinearMap v k
  have hL : ∀ (h : H k) (x : V k),
      L (ρ k h x) = FiniteTensor.external ρ (MonoidHom.mulSingle H k h) (L x) := by
    intro h x
    simp only [L, MultilinearMap.toLinearMap_apply, FiniteTensor.external_tprod]
    congr 1
    funext i
    by_cases hi : i = k
    · subst hi
      simp
    · rw [Function.update_of_ne hi, Function.update_of_ne hi, MonoidHom.mulSingle_apply,
        Pi.mulSingle_eq_of_ne hi, map_one, Module.End.one_apply]
  let F' : Representation.IntertwiningMap (ρ k)
      ((FiniteTensor.external τ).comp (MonoidHom.mulSingle H k)) :=
    { toLinearMap := f.toLinearMap ∘ₗ L
      isIntertwining' := by
        intro h
        ext x
        simp only [LinearMap.comp_apply, Representation.IntertwiningMap.coe_toLinearMap,
          MonoidHom.comp_apply, hL]
        exact Representation.IntertwiningMap.isIntertwining _ _ f _ _ }
  have hF : F' (v k) ≠ 0 := by
    change f (L (v k)) ≠ 0
    simpa [L] using hv
  refine exists_slot_ne_zero τ k (ρ k) F' fun h0 => hF ?_
  rw [h0]
  rfl

/-- If a nonzero `Z` embeds into an external tensor product whose factor at `k` is irreducible,
that factor is a quotient, hence a subquotient, of the restriction of `Z` to `H k`. -/
theorem isSubquotient_slot_of_injective [Fintype ι] (J : ∀ i, Representation ℂ (H i) (V i)) (k : ι)
    (hJ : (J k).IsIrreducible) {U : Type uU} [AddCommGroup U] [Module ℂ U] [Nontrivial U]
    (Z : Representation ℂ (∀ i, H i) U) (j : Z.IntertwiningMap (FiniteTensor.external J))
    (hj : Function.Injective j) :
    WeylBranchPieces.IsSubquotient (Z.comp (MonoidHom.mulSingle H k)) (J k) := by
  have := hJ
  let f : Representation.IntertwiningMap (Z.comp (MonoidHom.mulSingle H k))
      ((FiniteTensor.external J).comp (MonoidHom.mulSingle H k)) :=
    { toLinearMap := j.toLinearMap
      isIntertwining' := fun h => j.isIntertwining' (MonoidHom.mulSingle H k h) }
  have hf : f ≠ 0 := by
    intro h0
    obtain ⟨x, y, hxy⟩ := exists_pair_ne U
    apply hxy
    apply hj
    have hx : f x = 0 := by rw [h0]; rfl
    have hy : f y = 0 := by rw [h0]; rfl
    exact hx.trans hy.symm
  obtain ⟨g, hg⟩ := exists_slot_ne_zero J k _ f hf
  exact WeylBranchPieces.IsSubquotient.of_surjective g
    ((Representation.IsIrreducible.surjective_or_eq_zero g).resolve_right hg)

end Slots

section Injective

variable {G : Type uG} [Group G] {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

/-- The source of an injective intertwiner is a subquotient of its target. -/
theorem isSubquotient_of_injective {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (i : ρ.IntertwiningMap σ) (hi : Function.Injective i) : WeylBranchPieces.IsSubquotient σ ρ :=
  ⟨i.range, (JuxtaposedShuffle.rangeEquivOfInjective i hi).symm.toIntertwiningMap,
    (JuxtaposedShuffle.rangeEquivOfInjective i hi).symm.surjective⟩

end Injective

section Binary

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- An irreducible subquotient of `𝔄 ⊠ Y`, with `𝔄` irreducible, is equivalent to `𝔄 ⊠ E` for an
irreducible subquotient `E` of `Y`. -/
theorem exists_equiv_twoBlock_of_isSubquotient {a m : ℕ} (ha : 0 < a) (hm : 0 < m)
    {𝔄 : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier)}
    (h𝔄 : letI := T.topology; 𝔄.IsIrreducible)
    {Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)}
    (Z : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ
      ((BlockShape.ofPair a m ha hm rfl).Levi F.Carrier))
    (hZ : letI := T.topology; Z.IsIrreducible)
    (h : letI := T.topology; SmoothRep.IsSubquotient Z
      (FiniteTensor.externalSmoothObject (twoBlockFactors ha hm 𝔄 Y))) :
    letI := T.topology
    ∃ E : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier), E.IsIrreducible ∧
      SmoothRep.IsSubquotient E Y ∧
      Nonempty (Z.representation.Equiv
        (FiniteTensor.externalSmoothObject (twoBlockFactors ha hm 𝔄 E)).representation) := by
  let := T.topology
  have hZa : Z.IsAdmissible := CuspidalSupport.irreducibleLeviAdmissibility.{uF, max uF uV}
    F T (a + m) (BlockShape.ofPair a m ha hm rfl) Z hZ
  obtain ⟨X, hXi, -, ⟨eX⟩⟩ := CuspidalSupport.padicLeviAdmissibleFactorization.{uF, max uF uV}
    p F T (a + m) (by omega) (BlockShape.ofPair a m ha hm rfl) Z hZ hZa
  have hW : WeylBranchPieces.IsSubquotient
      (FiniteTensor.externalSmoothObject (twoBlockFactors ha hm 𝔄 Y)).representation
      Z.representation :=
    SmoothRep.isSubquotient_iff_representation.mp h
  have hnt : ∀ i, Nontrivial (X i) := fun i => nontrivial_of_isIrreducible (hXi i)
  have hslot : ∀ k : Fin (BlockShape.ofPair a m ha hm rfl).length,
      WeylBranchPieces.IsSubquotient (twoBlockFactors ha hm 𝔄 Y k).representation
        (X k).representation := by
    intro k
    have h1 := isSubquotient_external_comp_mulSingle
      (H := fun i => GeneralLinear ((BlockShape.ofPair a m ha hm rfl).size i) F.Carrier)
      (fun i => (X i).representation) hnt k
    have h2 := WeylBranchPieces.IsSubquotient.of_equiv_left
      (FiniteTensorFiltration.compCongr eX (MonoidHom.mulSingle
        (fun i => GeneralLinear ((BlockShape.ofPair a m ha hm rfl).size i) F.Carrier) k)) h1
    have h3 := (WeylBranchPieces.IsSubquotient.comp hW (MonoidHom.mulSingle
        (fun i => GeneralLinear ((BlockShape.ofPair a m ha hm rfl).size i) F.Carrier) k)).trans h2
    exact isSubquotient_factor_of_external_comp_mulSingle
      (H := fun i => GeneralLinear ((BlockShape.ofPair a m ha hm rfl).size i) F.Carrier)
      (fun i => (twoBlockFactors ha hm 𝔄 Y i).representation) k (X k).representation (hXi k) h3
  have h0 : WeylBranchPieces.IsSubquotient 𝔄.representation (X (0 : Fin 2)).representation :=
    hslot (0 : Fin 2)
  have h1 : WeylBranchPieces.IsSubquotient Y.representation (X (1 : Fin 2)).representation :=
    hslot (1 : Fin 2)
  obtain ⟨e0⟩ := CuspidalInductionJacquetConstituent.nonempty_equiv_of_isSubquotient h𝔄
    (hXi (0 : Fin 2)) h0
  refine ⟨X (1 : Fin 2), hXi (1 : Fin 2), SmoothRep.isSubquotient_iff_representation.mpr h1,
    ⟨eX.trans (FiniteTensorFiltration.externalCongr
      (@Fin.cases 1 (fun i => (X i).representation.Equiv
          (twoBlockFactors ha hm 𝔄 (X (1 : Fin 2)) i).representation) e0.symm
        (fun j => @Fin.cases 0 (fun j => (X j.succ).representation.Equiv
            (twoBlockFactors ha hm 𝔄 (X (1 : Fin 2)) j.succ).representation)
          (Representation.Equiv.refl _) (fun k => k.elim0) j)))⟩⟩

/-- **Frobenius reciprocity, converse direction.** A nonzero intertwiner from the Jacquet module
of an irreducible `π` along `(a, m)` to `𝔄 ⊠ E` gives an embedding of `π` into `𝔄 × E`. -/
theorem isSubrepresentation_of_jacquet_ne_zero {a m : ℕ} (ha : 0 < a) (hm : 0 < m)
    (π : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (a + m) F.Carrier))
    (hπ : letI := T.topology; π.IsIrreducible)
    (𝔄 : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
    (E : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier))
    (g : letI := T.topology
      (T.normalizedJacquet (BlockShape.ofPair a m ha hm rfl) π.representation).IntertwiningMap
        ((BlockShape.ofPair a m ha hm rfl).blockTensor
          (fun i => (twoBlockFactors ha hm 𝔄 E i).representation)))
    (hg : letI := T.topology; g ≠ 0) :
    letI := T.topology
    SmoothRep.IsSubrepresentation π ((T.binaryNormalizedProductFunctor a m).obj (𝔄, E)) := by
  let := T.topology
  obtain ⟨e⟩ := SegmentSocleDerivativesProof.nonempty_ofPairProductIso T ha hm 𝔄 E
  let B := BlockShape.ofPair a m ha hm rfl
  let adj := Parabolic.FirstAdjointness.equiv T B π.isSmooth
    (σ := FiniteTensor.external fun i => (twoBlockFactors ha hm 𝔄 E i).representation)
  let f₀ := adj.symm g
  let f : π ⟶ (T.binaryNormalizedProductFunctor a m).obj (𝔄, E) :=
    SmoothRep.ofHom f₀ ≫ e.inv
  have hf₀ : f₀ ≠ 0 := by
    intro h0
    apply hg
    rw [← adj.apply_symm_apply g]
    change adj f₀ = 0
    rw [h0]
    exact adj.map_zero
  have hf : SmoothRep.hom f ≠ 0 := by
    intro h0
    apply hf₀
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    apply SmoothRep.hom_hom_injective e.symm
    have h1 : SmoothRep.hom f v = 0 := by rw [h0]; rfl
    change SmoothRep.hom e.inv (f₀ v) = SmoothRep.hom e.inv 0
    rw [map_zero]
    exact h1
  have hπ' : π.representation.IsIrreducible := hπ
  rcases Representation.IsIrreducible.injective_or_eq_zero (SmoothRep.hom f) with h | h
  · exact ⟨f, h⟩
  · exact absurd h hf

/-- The Jacquet module of a subrepresentation of a normalized product induction is a
subquotient of the Jacquet–induction composite. -/
theorem isSubquotient_jacquetInduction_of_isSubrepresentation {n : ℕ} (C : BlockShape n)
    (X : letI := T.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (C.size i) F.Carrier))
    (P : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hs : letI := T.topology;
      SmoothRep.IsSubrepresentation P ((T.normalizedProductInductionFunctor C).obj X)) :
    letI := T.topology
    WeylBranchPieces.IsSubquotient
      ((jacquetInductionFunctor.{uF, max uF uV} T C C).obj
        (FiniteTensor.externalSmoothObject X)).ρ
      (T.normalizedJacquet C P.representation) := by
  let := T.topology
  obtain ⟨j, hj⟩ := hs
  have hinj := JuxtaposedShuffle.normalizedJacquetMap_injective T C
    ((T.normalizedProductInductionFunctor C).obj X).isSmooth (SmoothRep.hom j) hj
  exact isSubquotient_of_injective (T.normalizedJacquetMap C (SmoothRep.hom j)) hinj

/-- If `Z ≃ 𝔄 ⊠ E` embeds into `𝔄 ⊠ Y` and `E` is irreducible, then `E` embeds into `Y`. -/
theorem isSubrepresentation_of_twoBlock_equiv {a m : ℕ} (ha : 0 < a) (hm : 0 < m)
    {𝔄 : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier)}
    (h𝔄 : letI := T.topology; 𝔄.IsIrreducible)
    {Y E : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)}
    (hE : letI := T.topology; E.IsIrreducible) {U : Type uU} [AddCommGroup U] [Module ℂ U]
    {Z : Representation ℂ ((BlockShape.ofPair a m ha hm rfl).Levi F.Carrier) U}
    (j : letI := T.topology; Z.IntertwiningMap
      (FiniteTensor.externalSmoothObject (twoBlockFactors ha hm 𝔄 Y)).representation)
    (hj : Function.Injective j)
    (eZ : letI := T.topology;
      Z.Equiv (FiniteTensor.externalSmoothObject (twoBlockFactors ha hm 𝔄 E)).representation) :
    letI := T.topology
    SmoothRep.IsSubrepresentation E Y := by
  let := T.topology
  have hnt : ∀ i, Nontrivial (twoBlockFactors ha hm 𝔄 E i) := by
    intro i
    fin_cases i
    · exact nontrivial_of_isIrreducible h𝔄
    · exact nontrivial_of_isIrreducible hE
  have : Nontrivial (PiTensorProduct ℂ fun i => twoBlockFactors ha hm 𝔄 E i) :=
    FiniteTensor.nontrivial_piTensorProduct hnt
  let f := j.comp eZ.symm.toIntertwiningMap
  have hf : f ≠ 0 := by
    intro h0
    obtain ⟨x, hx⟩ := exists_ne (0 : PiTensorProduct ℂ fun i => twoBlockFactors ha hm 𝔄 E i)
    apply hx
    have h1 : f x = 0 := by rw [h0]; rfl
    have h2 : eZ.symm.toLinearEquiv x = 0 := hj (h1.trans (map_zero j).symm)
    exact eZ.symm.toLinearEquiv.map_eq_zero_iff.mp h2
  obtain ⟨g, hg⟩ := exists_slot_map_ne_zero
    (H := fun i => GeneralLinear ((BlockShape.ofPair a m ha hm rfl).size i) F.Carrier)
    (fun i => (twoBlockFactors ha hm 𝔄 E i).representation)
    (fun i => (twoBlockFactors ha hm 𝔄 Y i).representation) f hf (1 : Fin 2)
  let g' : E.representation.IntertwiningMap Y.representation := g
  have hE' : E.representation.IsIrreducible := hE
  rcases Representation.IsIrreducible.injective_or_eq_zero g' with h | h
  · exact ⟨SmoothRep.ofHom g', h⟩
  · exact absurd h hg

/-- **The comparison step.** Let `A` be supercuspidal on `GL_d`, `𝔄` irreducible and `A`-pure on
`GL_a`, and `Y` left `A`-reduced on `GL_m` (`d, a, m > 0`). Every irreducible
subrepresentation `π` of `𝔄 × Y` embeds into `𝔄 × E` for some irreducible subrepresentation `E`
of `Y`. -/
theorem exists_isSubrepresentation_of_isSubrepresentation_binaryProduct {d a m : ℕ}
    (hd : 0 < d) (ha : 0 < a) (hm : 0 < m)
    (A : letI := T.topology; SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := d))
    {𝔄 : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier)}
    (h𝔄 : letI := T.topology; 𝔄.IsIrreducible) (hp : IsPure T hd A 𝔄)
    {Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)}
    (hr : LeftReduced F T A Y)
    {π : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (a + m) F.Carrier)}
    (hπ : letI := T.topology; π.IsIrreducible)
    (hs : letI := T.topology;
      SmoothRep.IsSubrepresentation π ((T.binaryNormalizedProductFunctor a m).obj (𝔄, Y))) :
    letI := T.topology
    ∃ E : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier), E.IsIrreducible ∧
      SmoothRep.IsSubrepresentation E Y ∧
      SmoothRep.IsSubrepresentation π ((T.binaryNormalizedProductFunctor a m).obj (𝔄, E)) := by
  let := T.topology
  have hπnt : Nontrivial π := nontrivial_of_isIrreducible hπ
  obtain ⟨g, hg⟩ := exists_jacquet_ne_zero_of_isSubrepresentation F T ha hm rfl π 𝔄 Y hπnt hs
  have hJfl := (Parabolic.normalizedParabolicFiniteLength.{uF, max uF uV} F T).2 (a + m)
    (BlockShape.ofPair a m ha hm rfl) π (SmoothRep.hasFiniteLength_of_isIrreducible hπ)
  let gS : (T.normalizedJacquetFunctor.{uF, max uF uV} (BlockShape.ofPair a m ha hm rfl)).obj π ⟶
      FiniteTensor.externalSmoothObject (twoBlockFactors ha hm 𝔄 Y) :=
    SmoothRep.ofHom g
  have hgS : SmoothRep.hom gS ≠ 0 := hg
  -- an irreducible quotient of the image of `g` is `𝔄 ⊠ E`, so `π ↪ 𝔄 × E`
  obtain ⟨Z', hZ', ⟨q, hq⟩, hZ'W⟩ :=
    SmoothRep.exists_irreducible_quotient_subquotient_of_nonzero hJfl gS hgS
  obtain ⟨E, hE, hEY, ⟨eZ'⟩⟩ := exists_equiv_twoBlock_of_isSubquotient F T ha hm h𝔄 Z' hZ' hZ'W
  have hsE : SmoothRep.IsSubrepresentation π
      ((T.binaryNormalizedProductFunctor a m).obj (𝔄, E)) := by
    have hZ'nt : Nontrivial Z' := nontrivial_of_isIrreducible hZ'
    refine isSubrepresentation_of_jacquet_ne_zero F T ha hm π hπ 𝔄 E
      (eZ'.toIntertwiningMap.comp (SmoothRep.hom q)) ?_
    intro h0
    obtain ⟨z, hz⟩ := exists_ne (0 : Z')
    obtain ⟨v, rfl⟩ := hq z
    apply hz
    have h1 : eZ'.toLinearEquiv (SmoothRep.hom q v) = 0 := by
      have := congrArg (fun f => f v) h0
      exact this
    exact eZ'.toLinearEquiv.map_eq_zero_iff.mp h1
  have hEr : LeftReduced F T A E := leftReduced_of_isSubquotient F T A hEY hr
  -- an irreducible subrepresentation of the image of `g` is `𝔄 ⊠ E`, so `E ↪ Y`
  obtain ⟨Z, hZ, hZJ, ⟨j, hj⟩⟩ := exists_irreducible_of_hom_ne_zero hJfl gS hgS
  have hZnt : Nontrivial Z := nontrivial_of_isIrreducible hZ
  have h𝔄Z := isSubquotient_slot_of_injective
    (H := fun i => GeneralLinear ((BlockShape.ofPair a m ha hm rfl).size i) F.Carrier)
    (fun i => (twoBlockFactors ha hm 𝔄 Y i).representation) (0 : Fin 2) h𝔄 Z.representation
    (SmoothRep.hom j) hj
  have hsub2 : SmoothRep.IsSubrepresentation π
      ((T.normalizedProductInductionFunctor (BlockShape.ofPair a m ha hm rfl)).obj
        (twoBlockFactors ha hm 𝔄 E)) := by
    obtain ⟨e⟩ := SegmentSocleDerivativesProof.nonempty_ofPairProductIso T ha hm 𝔄 E
    exact isSubrepresentation_of_iso T hsE e
  have hZsq := (isSubquotient_jacquetInduction_of_isSubrepresentation F T
    (BlockShape.ofPair a m ha hm rfl) (twoBlockFactors ha hm 𝔄 E) π hsub2).trans
    (SmoothRep.isSubquotient_iff_representation.mp hZJ)
  obtain ⟨eZ⟩ := nonempty_equiv_of_isSubquotient_jacquetInduction F T hd ha hm A h𝔄 hp hE hEr
    hZ hZsq h𝔄Z
  exact ⟨E, hE, isSubrepresentation_of_twoBlock_equiv F T ha hm h𝔄 hE (SmoothRep.hom j) hj eZ,
    hsE⟩

end Binary

end Langlands.Classification.LeftCuspidalDerivative
