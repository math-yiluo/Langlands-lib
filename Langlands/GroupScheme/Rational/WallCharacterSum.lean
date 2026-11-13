import Langlands.LinearAlgebra.InvariantFormComplements
import Langlands.GroupScheme.Rational.RelativeCentralDirections
import Langlands.GroupScheme.Rational.RelativeCharacterRootComplementProof
import Langlands.GroupScheme.Rational.RelativeSplitCentralDirectionsProof
import Langlands.GroupScheme.Rational.RootReflectionExistenceProof
import Langlands.GroupScheme.Rational.RootKernelTorus
import Langlands.GroupScheme.Rational.RelativeWeylRootKernel
import Langlands.GroupScheme.Rational.ReductiveWeylFaithfulness
import Langlands.GroupScheme.Rational.SplitTorusRationalRank
import Langlands.GroupScheme.Rational.ParabolicLeviTorusConjugation
import Langlands.GroupScheme.Rational.MaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Rational.TorusSplitPartTransfer
import Langlands.GroupScheme.Rational.MaximalLeviCentralKernel
import Langlands.GroupScheme.Rational.MaximalLeviConeComplementLine
import Langlands.GroupScheme.Rational.WeylTorusNorm
import Langlands.GroupScheme.Rational.SplitTorusFactorization
import Langlands.GroupScheme.Rational.SplitComponentProof
import Langlands.GroupScheme.Rational.CharacterRestrictionProof
import Langlands.GroupScheme.Rational.LeviSubgroup
import Langlands.Geometry.Building.CocharacterUniformizerProof

/-! # Rational characters of a common Levi across a rank-one wall -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.LinearAlgebra.RationalSpan
open Langlands.LinearAlgebra.InvariantFormComplements

namespace Langlands.GroupScheme.WallCharacterSum

variable {k : Type u} [Field k]

section Pairing

variable {A : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Evaluation of rationalized characters of `A` on an integral cocharacter. -/
def ratPairing (ν : cocharacterLattice A) : (ℚ ⊗[ℤ] characterLattice A) →ₗ[ℚ] ℚ :=
  (TensorProduct.AlgebraTensorModule.rid ℤ ℚ ℚ).toLinearMap.comp
    (((latticePairing A).flip ν).baseChange ℚ)

theorem ratPairing_tmul (ν : cocharacterLattice A) (q : ℚ) (χ : characterLattice A) :
    ratPairing ν (q ⊗ₜ[ℤ] χ) = q * (latticePairing A χ ν : ℚ) := by
  simp [ratPairing, zsmul_eq_mul, mul_comm]

/-- The rational pairing is additive and `ℤ`-homogeneous in the cocharacter. -/
theorem ratPairing_zsmul_sub (a b : ℤ) (ν ν₁ : cocharacterLattice A)
    (y : ℚ ⊗[ℤ] characterLattice A) :
    ratPairing (a • ν - b • ν₁) y = a * ratPairing ν y - b * ratPairing ν₁ y := by
  induction y using TensorProduct.inductionOn with
  | tmul q χ =>
    simp only [ratPairing_tmul, map_sub, map_zsmul, smul_eq_mul, Int.cast_sub, Int.cast_mul]
    ring
  | add y z hy hz =>
    rw [map_add, map_add, map_add, hy, hz]
    ring

/-- On a split torus, a rationalized character vanishing on all integral cocharacters
is zero. -/
theorem eq_zero_of_ratPairing (hA : IsSplitTorus A.toGrp) {y : ℚ ⊗[ℤ] characterLattice A}
    (hy : ∀ ν, ratPairing ν y = 0) : y = 0 := by
  obtain ⟨n, hn, χ, hχ⟩ := exists_nsmul_eq_one_tmul y
  have hperf := CocharacterUniformizer.latticePairing_isPerfPair k A hA
  have hχ0 : χ = 0 := by
    apply (LinearMap.IsPerfPair.bijective_left (latticePairing A)).injective
    rw [map_zero]
    refine LinearMap.ext fun ν => ?_
    have h := congrArg (ratPairing ν) hχ
    rw [map_smul, hy, smul_zero, ratPairing_tmul, one_mul, eq_comm, Int.cast_eq_zero] at h
    exact h
  rw [hχ0, TensorProduct.tmul_zero] at hχ
  exact (smul_eq_zero.mp hχ).resolve_left (by exact_mod_cast hn.ne')

end Pairing

section RootSpan

variable {A T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- Roots restricted along a factorization `f ≫ i = m` vanish on cocharacters whose
composite with `m` is central; extended linearly to the rational root span. -/
theorem ratPairing_restrict_eq_zero_of_isCentral [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (i : T.toGrp ⟶ G) (f : A ⟶ T) {m : A.toGrp ⟶ G}
    (hf : CommGroupScheme.groupHom f ≫ i = m) {ν : cocharacterLattice A}
    (hν : IsCentral (CommGroupScheme.groupHom ν ≫ m)) {x : ℚ ⊗[ℤ] characterLattice T}
    (hx : x ∈ relativeRootSpan i) :
    ratPairing ν (rationalCharacterRestrictRat (CommGroupScheme.groupHom f) x) = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨β, hβ, rfl⟩ := hy
    rw [toRat_apply, rationalCharacterRestrictRat_tmul, ratPairing_tmul, one_mul,
      Int.cast_eq_zero]
    exact MaximalLeviConeComplementLine.latticePairing_restrict_eq_zero_of_isCentral i f hf hβ hν
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, map_add, hy, hz, add_zero]
  | smul c y _ hy => rw [map_smul, map_smul, hy, smul_zero]

/-- For a maximal split torus `iH` of a connected reductive `H` and `iH ≫ j = iG`, a form
invariant under the full relative Weyl action of `iG` makes the rationalized restrictions
of characters of `H` orthogonal to the relative root span of `iH`. -/
theorem restrict_orthogonal_rootSpan (hH : IsConnectedReductive H) {iH : T.toGrp ⟶ H}
    (hiH : IsMaximalSplitTorus iH) (j : H ⟶ G) (iG : T.toGrp ⟶ G) (hij : iH ≫ j = iG)
    [Mono iG.hom.hom.left] (B : LinearMap.BilinForm ℚ (ℚ ⊗[ℤ] characterLattice T))
    (hB : ∀ w x y, B (relativeWeylFullRatAction iG w x) (relativeWeylFullRatAction iG w y) =
      B x y) :
    haveI := hH.isAffineHom
    ∀ v ∈ (rationalCharacterRestrictRat iH).range, ∀ s ∈ relativeRootSpan iH, B v s = 0 := by
  have := hH.isAffineHom
  have := hiH.isSplitSubtorus.mono
  obtain ⟨D, -⟩ := relativeRootReflectionExistence k H hH T iH hiH
  rintro v ⟨y, rfl⟩ s hs
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨α, hα, rfl⟩ := hx
    let n := normalizerPointsMap iH j iG hij (D.representative ⟨α, hα⟩)
    have hw : relativeWeylFullRatAction iG (QuotientGroup.mk n) =
        ratAut (weylAction iH (D.representative ⟨α, hα⟩)) := by
      rw [relativeWeylFullRatAction_mk, weylAction_normalizerPointsMap]
    refine apply_eq_zero_of_fixed_of_neg B _ (hB (QuotientGroup.mk n)) ?_ ?_
    · rw [hw]
      induction y using TensorProduct.inductionOn with
      | tmul q χ =>
        exact (ratAut_tmul _ q _).trans
          (congrArg (q ⊗ₜ[ℤ] ·) (weylAction_torusCharacterRestrict iH _ χ))
      | add y z hy hz => rw [map_add, map_add, hy, hz]
    · rw [hw, toRat_apply]
      refine (ratAut_tmul _ 1 α).trans ?_
      have h2 : latticePairing T α (D.coroot ⟨α, hα⟩) = 2 := D.pair_self ⟨α, hα⟩
      rw [D.action, h2]
      change (1 : ℚ) ⊗ₜ[ℤ] (α - (2 : ℤ) • α) = _
      rw [show α - (2 : ℤ) • α = -α by abel, TensorProduct.tmul_neg]
  | zero => simp
  | add x z _ _ hx hz => rw [map_add, hx, hz, add_zero]
  | smul c x _ hx => rw [map_smul, hx, smul_zero]

end RootSpan

section Wall

variable {T A : CommGroupScheme (Spec (CommRingCat.of k))}
  {L Q M Q₁ M₁ : GroupScheme (Spec (CommRingCat.of k))}

/-- Across a rank-one wall, the relative root spans of `M` and `M₁` for a common maximal
split torus of `L` meet inside the relative root span of `L`. -/
theorem rootSpan_inf_le_of_wall (hM : IsConnectedReductive M) (hM₁ : IsConnectedReductive M₁)
    {q : Q ⟶ M} {l : L ⟶ Q} {q₁ : Q₁ ⟶ M₁} {l₁ : L ⟶ Q₁}
    (hq : IsParabolicSubgroup q) (hl : IsRationalLeviSubgroup l)
    (hq₁ : IsParabolicSubgroup q₁) (hl₁ : IsRationalLeviSubgroup l₁) (hne : ¬ IsIso q₁)
    (hmax : ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (h : H ⟶ M₁) (f : Q₁ ⟶ H),
      IsParabolicSubgroup h → f ≫ h = q₁ → IsIso f ∨ IsIso h)
    {a : A.toGrp ⟶ M} {b : A.toGrp ⟶ L} (ha : IsSplitComponent a) (hb : b ≫ l ≫ q = a)
    (hnc : ¬ IsCentral (b ≫ l₁ ≫ q₁)) {iL : T.toGrp ⟶ L} (hiL : IsMaximalSplitTorus iL) :
    haveI := hl.isConnectedReductive.isAffineHom
    haveI := hM.isAffineHom
    haveI := hM₁.isAffineHom
    relativeRootSpan (iL ≫ l ≫ q) ⊓ relativeRootSpan (iL ≫ l₁ ≫ q₁) ≤
      relativeRootSpan iL := by
  have hL := hl.isConnectedReductive
  have := hL.isAffineHom
  have := hM.isAffineHom
  have := hM₁.isAffineHom
  have : Smooth M.X.hom := hM.smooth
  have : Smooth M₁.X.hom := hM₁.smooth
  obtain ⟨AL, aL, haL⟩ := (splitComponentStatement k L hL).1
  obtain ⟨f, hf, -, -, -, hker, -⟩ :=
    (relativeSplitCentralDirections k L hL T iL hiL).2.2.2.2.2.2 AL aL haL
  obtain ⟨α₀, hα₀⟩ :=
    hasCentralKernelCharacter_of_maximal parabolicDynamic hM₁ hq₁ hl₁ hne hmax haL
  have : IsClosedImmersion q.hom.hom.left := hq.isClosedSubgroup
  have : IsClosedImmersion l.hom.hom.left := hl.isClosedSubgroup
  have hbc : IsCentral b := by
    refine IsCentral.of_comp (j := l) (Over.mono_of_mono_left _) ?_
    refine IsCentral.of_comp (j := q) (Over.mono_of_mono_left _) ?_
    rw [Category.assoc, hb]
    exact ha.1.2
  obtain ⟨c, hc⟩ := haL.exists_factor ha.1.1.1 hbc
  obtain ⟨ε, hε⟩ : ∃ ε : cocharacterLattice A,
      ¬ IsCentral (CommGroupScheme.groupHom ε ≫ b ≫ l₁ ≫ q₁) := by
    by_contra h
    push Not at h
    exact hnc (isCentral_of_forall_cocharacter ha.1.1.1 _ h)
  let ε₀ : cocharacterLattice AL := ε ≫ Additive.ofMul c
  have hε₀ : ∀ {X : GroupScheme (Spec (CommRingCat.of k))} (g : L ⟶ X),
      CommGroupScheme.groupHom ε₀ ≫ aL ≫ g = CommGroupScheme.groupHom ε ≫ b ≫ g := by
    intro X g
    change (CommGroupScheme.groupHom ε ≫ c) ≫ aL ≫ g = _
    rw [Category.assoc, ← Category.assoc c, hc]
  have hcentM : IsCentral (CommGroupScheme.groupHom ε₀ ≫ aL ≫ l ≫ q) := by
    rw [hε₀, hb]
    exact ha.1.2.comp _
  have ha₀ : latticePairing AL α₀ ε₀ ≠ 0 := by
    intro h
    exact hε (hε₀ (l₁ ≫ q₁) ▸ hα₀ ε₀ h)
  intro x hx
  rw [← hker, LinearMap.mem_ker]
  apply eq_zero_of_ratPairing haL.1.1.1
  intro ν
  have h₁ := ratPairing_restrict_eq_zero_of_isCentral (iL ≫ l ≫ q) f
    (m := aL ≫ l ≫ q) (by rw [← Category.assoc, hf]) hcentM hx.1
  have h₂ := ratPairing_restrict_eq_zero_of_isCentral (iL ≫ l₁ ≫ q₁) f
    (m := aL ≫ l₁ ≫ q₁) (by rw [← Category.assoc, hf])
    (hα₀ (latticePairing AL α₀ ε₀ • ν - latticePairing AL α₀ ν • ε₀) (by
      rw [map_sub, map_zsmul, map_zsmul, smul_eq_mul, smul_eq_mul, mul_comm, sub_self]))
    hx.2
  rw [ratPairing_zsmul_sub, h₁, mul_zero, sub_zero] at h₂
  exact (mul_eq_zero.mp h₂).resolve_left (by exact_mod_cast ha₀)

end Wall

section Assembly

variable {T A : CommGroupScheme (Spec (CommRingCat.of k))}
  {G P M Q L P₁ M₁ Q₁ : GroupScheme (Spec (CommRingCat.of k))}

/-- Restriction of rational characters of a connected reductive group to a maximal split
torus is injective. -/
theorem characterRestrict_injective (hL : IsConnectedReductive L) {iL : T.toGrp ⟶ L}
    (hiL : IsMaximalSplitTorus iL) : Function.Injective (characterRestrict iL) := by
  have := hL.isAffineHom
  have := hiL.isSplitSubtorus.mono
  obtain ⟨AL, aL, haL⟩ := (splitComponentStatement k L hL).1
  obtain ⟨f, hf, -⟩ :=
    (relativeSplitCentralDirections k L hL T iL hiL).2.2.2.2.2.2 AL aL haL
  have h := (characterRestriction k L hL AL aL haL).1
  rw [← hf, characterRestrict_comp, AddMonoidHom.coe_comp] at h
  exact h.of_comp

/-- If the rationalized restrictions to a split torus of the characters of `L` lie in the sum
of those of `M` and `M₁`, then a positive multiple of each character of `L` is a sum of
restrictions, provided restriction to the torus is injective. -/
theorem exists_nsmul_eq_restrict_add_of_le_sup {iL : T.toGrp ⟶ L} (hT : IsSplitTorus T.toGrp)
    (hinj : Function.Injective (characterRestrict iL)) {f : L ⟶ M} {g : L ⟶ M₁}
    (h : LinearMap.range (rationalCharacterRestrictRat iL) ≤
      LinearMap.range (rationalCharacterRestrictRat (iL ≫ f)) ⊔
        LinearMap.range (rationalCharacterRestrictRat (iL ≫ g)))
    (χ : rationalCharacters L) :
    ∃ n : ℕ, 0 < n ∧ ∃ (ψ : rationalCharacters M) (ψ₁ : rationalCharacters M₁),
      n • χ = characterRestrict f ψ + characterRestrict g ψ₁ := by
  obtain ⟨y, ⟨y', rfl⟩, z, ⟨z', rfl⟩, hyz⟩ :=
    Submodule.mem_sup.mp (h (LinearMap.mem_range_self _ (toRat χ)))
  obtain ⟨n, hn, ψ, hψ⟩ := exists_nsmul_eq_one_tmul y'
  obtain ⟨n₁, hn₁, ψ₁, hψ₁⟩ := exists_nsmul_eq_one_tmul z'
  refine ⟨n * n₁, Nat.mul_pos hn hn₁, n₁ • ψ, n • ψ₁,
    hinj (hT.character_toRat_injective ?_)⟩
  have e₁ : rationalCharacterRestrictRat (iL ≫ f) ((n : ℚ) • y') =
      toRat (characterRestrict iL (characterRestrict f ψ)) := by
    rw [hψ, rationalCharacterRestrictRat_tmul, characterRestrict_comp,
      AddMonoidHom.comp_apply]
    rfl
  have e₂ : rationalCharacterRestrictRat (iL ≫ g) ((n₁ : ℚ) • z') =
      toRat (characterRestrict iL (characterRestrict g ψ₁)) := by
    rw [hψ₁, rationalCharacterRestrictRat_tmul, characterRestrict_comp,
      AddMonoidHom.comp_apply]
    rfl
  have e₀ : rationalCharacterRestrictRat iL (toRat χ) = toRat (characterRestrict iL χ) := rfl
  change toRat (characterRestrict iL ((n * n₁) • χ)) =
    toRat (characterRestrict iL (characterRestrict f (n₁ • ψ) + characterRestrict g (n • ψ₁)))
  simp only [map_nsmul, map_add]
  rw [← e₀, ← e₁, ← e₂, ← hyz, map_smul, map_smul, Nat.cast_smul_eq_nsmul ℚ,
    Nat.cast_smul_eq_nsmul ℚ, smul_add, smul_smul, smul_smul, mul_comm n₁ n]

/-- With a maximal split torus of `G` lying in `L` and maximal split in `L`, `M` and `M₁`,
the rationalized restrictions of characters of `L` to the torus lie in the sum of those of
`M` and `M₁`. -/
theorem restrictRange_le_sup (hG : IsConnectedReductive G)
    {p : P ⟶ G} {m : M ⟶ P} {q : Q ⟶ M} {l : L ⟶ Q}
    {p₁ : P₁ ⟶ G} {m₁ : M₁ ⟶ P₁} {q₁ : Q₁ ⟶ M₁} {l₁ : L ⟶ Q₁}
    (hm : IsRationalLeviSubgroup m) (hq : IsParabolicSubgroup q) (hl : IsRationalLeviSubgroup l)
    (hm₁ : IsRationalLeviSubgroup m₁) (hq₁ : IsParabolicSubgroup q₁)
    (hl₁ : IsRationalLeviSubgroup l₁)
    (hcomm : l ≫ q ≫ m ≫ p = l₁ ≫ q₁ ≫ m₁ ≫ p₁) (hne : ¬ IsIso q₁)
    (hmax : ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (h : H ⟶ M₁) (f : Q₁ ⟶ H),
      IsParabolicSubgroup h → f ≫ h = q₁ → IsIso f ∨ IsIso h)
    {a : A.toGrp ⟶ M} {b : A.toGrp ⟶ L} (ha : IsSplitComponent a) (hb : b ≫ l ≫ q = a)
    (hnc : ¬ IsCentral (b ≫ l₁ ≫ q₁)) {iL : T.toGrp ⟶ L} (hiL : IsMaximalSplitTorus iL)
    (hiM : IsMaximalSplitTorus (iL ≫ l ≫ q)) (hiM₁ : IsMaximalSplitTorus (iL ≫ l₁ ≫ q₁))
    (hiG : IsMaximalSplitTorus (iL ≫ l ≫ q ≫ m ≫ p)) :
    LinearMap.range (rationalCharacterRestrictRat iL) ≤
      LinearMap.range (rationalCharacterRestrictRat (iL ≫ l ≫ q)) ⊔
        LinearMap.range (rationalCharacterRestrictRat (iL ≫ l₁ ≫ q₁)) := by
  have hM := hm.isConnectedReductive
  have hM₁ := hm₁.isConnectedReductive
  have hL := hl.isConnectedReductive
  have := hiG.isSplitSubtorus.mono
  have := hG.finite_relativeWeylGroup _ hiG
  have := hiG.isSplitSubtorus.1.finite_characterLatticeRat
  obtain ⟨B, hB, hBinv⟩ :=
    exists_invariant_anisotropic (relativeWeylFullRatAction (iL ≫ l ≫ q ≫ m ≫ p))
  have h₁ := (relativeCharacterRootComplement k M hM T _ hiM).1.sup_eq_top
  have h₂ := (relativeCharacterRootComplement k M₁ hM₁ T _ hiM₁).1.sup_eq_top
  rw [sup_comm] at h₁ h₂
  exact le_sup_of_anisotropic B hB h₁ h₂
    (restrict_orthogonal_rootSpan hM hiM (m ≫ p) _ (by simp only [Category.assoc]) B hBinv)
    (restrict_orthogonal_rootSpan hM₁ hiM₁ (m₁ ≫ p₁) _
      (by simp only [Category.assoc, hcomm]) B hBinv)
    (restrict_orthogonal_rootSpan hL hiL (l ≫ q ≫ m ≫ p) _ rfl B hBinv)
    (rootSpan_inf_le_of_wall hM hM₁ hq hl hq₁ hl₁ hne hmax ha hb hnc hiL)

/-- For a Levi `L` of a parabolic of a Levi `M` of a parabolic of a connected reductive `G`,
some maximal split torus of `G` factors through `L`. -/
theorem exists_maximalSplitTorus_factor_levi (hG : IsConnectedReductive G)
    {p : P ⟶ G} {m : M ⟶ P} {q : Q ⟶ M} {l : L ⟶ Q}
    (hp : IsParabolicSubgroup p) (hm : IsRationalLeviSubgroup m)
    (hq : IsParabolicSubgroup q) (hl : IsRationalLeviSubgroup l) :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (iL : T.toGrp ⟶ L),
      IsMaximalSplitTorus (iL ≫ l ≫ q ≫ m ≫ p) := by
  have hM := hm.isConnectedReductive
  have hmp : IsClosedSubgroup (m ≫ p) := hm.isClosedSubgroup.comp hp.isClosedSubgroup
  obtain ⟨T₁, i₁, hi₁, a₁, ha₁⟩ :=
    ParabolicLeviTorus.exists_maximalSplitTorus_factor parabolicDynamic hG hp hm
  have ha₁M : IsMaximalSplitTorus a₁ := IsMaximalSplitTorus.of_comp hmp (ha₁ ▸ hi₁)
  obtain ⟨T, i₀, hi₀, a₀, ha₀⟩ :=
    ParabolicLeviTorus.exists_maximalSplitTorus_factor parabolicDynamic hM hq hl
  obtain ⟨g, e, he⟩ := (maximalSplitTorusConjugacy k M hM).1 T T₁ i₀ a₁ hi₀ ha₁M
  refine ⟨T, a₀, ?_⟩
  have h₀ : a₀ ≫ l ≫ q ≫ m ≫ p = i₀ ≫ m ≫ p := by
    rw [← ha₀]
    simp only [Category.assoc]
  rw [h₀]
  let X := G.innerIso (g ≫ (m ≫ p).hom.hom)
  have h₁ : i₀ ≫ (m ≫ p) ≫ X.hom = e.hom ≫ i₁ := by
    rw [comp_innerIso_hom_comp, ← Category.assoc, he, Category.assoc, ha₁]
  refine IsMaximalSplitTorus.of_factor (hi₁.comp_iso X.symm) (hi₀.1.comp hmp) e.inv ?_
  rw [Iso.symm_hom, Iso.eq_comp_inv]
  simp only [Category.assoc] at h₁ ⊢
  rw [h₁, Iso.inv_hom_id_assoc]

/-- Across a rank-one wall, a positive multiple of every rational character of the common
Levi `L` is the sum of restrictions of rational characters of `M` and `M₁`. -/
theorem exists_nsmul_eq_restrict_add (hG : IsConnectedReductive G)
    {p : P ⟶ G} {m : M ⟶ P} {q : Q ⟶ M} {l : L ⟶ Q}
    {p₁ : P₁ ⟶ G} {m₁ : M₁ ⟶ P₁} {q₁ : Q₁ ⟶ M₁} {l₁ : L ⟶ Q₁}
    (hp : IsParabolicSubgroup p) (hm : IsRationalLeviSubgroup m)
    (hq : IsParabolicSubgroup q) (hl : IsRationalLeviSubgroup l)
    (hp₁ : IsParabolicSubgroup p₁) (hm₁ : IsRationalLeviSubgroup m₁)
    (hq₁ : IsParabolicSubgroup q₁) (hl₁ : IsRationalLeviSubgroup l₁)
    (hcomm : l ≫ q ≫ m ≫ p = l₁ ≫ q₁ ≫ m₁ ≫ p₁) (hne : ¬ IsIso q₁)
    (hmax : ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (h : H ⟶ M₁) (f : Q₁ ⟶ H),
      IsParabolicSubgroup h → f ≫ h = q₁ → IsIso f ∨ IsIso h)
    {a : A.toGrp ⟶ M} {b : A.toGrp ⟶ L} (ha : IsSplitComponent a) (hb : b ≫ l ≫ q = a)
    (hnc : ¬ IsCentral (b ≫ l₁ ≫ q₁)) (χ : rationalCharacters L) :
    ∃ n : ℕ, 0 < n ∧ ∃ (ψ : rationalCharacters M) (ψ₁ : rationalCharacters M₁),
      n • χ = characterRestrict (l ≫ q) ψ + characterRestrict (l₁ ≫ q₁) ψ₁ := by
  obtain ⟨T, iL, hiG⟩ := exists_maximalSplitTorus_factor_levi hG hp hm hq hl
  have hiM : IsMaximalSplitTorus (iL ≫ l ≫ q) := by
    refine IsMaximalSplitTorus.of_comp (hm.isClosedSubgroup.comp hp.isClosedSubgroup) ?_
    simpa only [Category.assoc] using hiG
  have hiM₁ : IsMaximalSplitTorus (iL ≫ l₁ ≫ q₁) := by
    refine IsMaximalSplitTorus.of_comp (hm₁.isClosedSubgroup.comp hp₁.isClosedSubgroup) ?_
    simpa only [Category.assoc, hcomm] using hiG
  have hiL : IsMaximalSplitTorus iL :=
    IsMaximalSplitTorus.of_comp (hl.isClosedSubgroup.comp hq.isClosedSubgroup) hiM
  exact exists_nsmul_eq_restrict_add_of_le_sup hiL.1.1
    (characterRestrict_injective hl.isConnectedReductive hiL)
    (restrictRange_le_sup hG hm hq hl hm₁ hq₁ hl₁ hcomm hne hmax ha hb hnc hiL hiM hiM₁ hiG) χ

end Assembly

end Langlands.GroupScheme.WallCharacterSum
