import Langlands.Representation.Intertwining.PQOuterLeviRadicals
import Langlands.Representation.Intertwining.PQIdentitySupportProof
import Langlands.Representation.Geometric.CosetOrbitHomeomorph
import Langlands.Representation.Geometric.ClosedSubgroupOrbitOrdering
import Langlands.GroupScheme.Rational.ParabolicDoubleCosetProof

/-! # Support of `P₁P₂` inside `Q₁Q₂` (Renard VII.3.5 (iii))

For nested represented parabolics `P₁ ⊂ Q₁ = LU₁`, `P₂ ⊂ Q₂ = LU₂` with
`P₁(F) ∩ L(F) = P₂(F) ∩ L(F)`, the double coset `P₁(F)P₂(F)` is relatively closed in
`Q₁(F)Q₂(F)`: `closure (P₁P₂) ∩ Q₁Q₂ ⊆ P₁P₂`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

section Abstract

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Abstract form: if `Q₂` acts with open orbit map on the orbit of `P₁` in `P₁ \ H`,
`P₂ ≤ Q₂` is closed and `P₁ ∩ Q₂ ≤ P₂`, then `P₁P₂` is relatively closed in `P₁Q₂`. -/
theorem doubleCoset_mem_of_mem_closure {P₁ P₂ Q₂ : Subgroup H}
    (hP₂ : IsClosed (P₂ : Set H)) (hP₂Q₂ : P₂ ≤ Q₂) (hint : P₁ ⊓ Q₂ ≤ P₂)
    (hopen : IsOpenMap (Geometric.cosetOrbitMap P₁ Q₂ 1)) {g : H}
    (hg : g ∈ closure (DoubleCoset.quotToDoubleCoset P₁ P₂ (DoubleCoset.mk P₁ P₂ 1)))
    (hgQ : DoubleCoset.mk P₁ Q₂ g = DoubleCoset.mk P₁ Q₂ 1) :
    DoubleCoset.mk P₁ P₂ g = DoubleCoset.mk P₁ P₂ 1 := by
  by_contra hne
  obtain ⟨p, hp, b, hb, hgb⟩ := DoubleCoset.eq.mp hgQ.symm
  have hbP₂ : b ∉ P₂ := fun h => hne (DoubleCoset.eq.mpr ⟨p, hp, b, h, hgb⟩).symm
  let Ω : Set Q₂ := {c | (c : H) ∉ P₂}
  have hΩ : IsOpen Ω := (hP₂.preimage continuous_subtype_val).isOpen_compl
  obtain ⟨Wq, hWq, hWqeq⟩ := isOpen_induced_iff.mp (hopen Ω hΩ)
  let W : Set H := Induction.quotientMap P₁ ⁻¹' Wq
  have hW : IsOpen W := hWq.preimage
    (QuotientIntegration.leftQuotient_isOpenQuotientMap P₁).continuous
  have hgW : g ∈ W := by
    have hmem : Geometric.cosetOrbitMap P₁ Q₂ 1 ⟨b, hb⟩ ∈
        Geometric.cosetOrbitMap P₁ Q₂ 1 '' Ω := ⟨⟨b, hb⟩, hbP₂, rfl⟩
    rw [← hWqeq] at hmem
    have hq : Induction.quotientMap P₁ g = Induction.quotientMap P₁ (1⁻¹ * b) := by
      apply Quotient.sound
      change QuotientGroup.rightRel P₁ g (1⁻¹ * b)
      rw [QuotientGroup.rightRel_apply, hgb]
      simpa [mul_assoc] using P₁.inv_mem hp
    show Induction.quotientMap P₁ g ∈ Wq
    rw [hq]
    exact hmem
  obtain ⟨h, hhW, hhP⟩ := mem_closure_iff.mp hg W hW hgW
  rw [DoubleCoset.mem_quotToDoubleCoset_iff] at hhP
  obtain ⟨p', hp', b', hb', hh⟩ := DoubleCoset.eq.mp hhP.symm
  have hmem' : Geometric.cosetOrbitMap P₁ Q₂ 1 ⟨b', hP₂Q₂ hb'⟩ ∈
      (Subtype.val ⁻¹' Wq : Set (Geometric.cosetOrbit P₁ Q₂ 1)) := by
    have hq : Induction.quotientMap P₁ h = Induction.quotientMap P₁ (1⁻¹ * b') := by
      apply Quotient.sound
      change QuotientGroup.rightRel P₁ h (1⁻¹ * b')
      rw [QuotientGroup.rightRel_apply, hh]
      simpa [mul_assoc] using P₁.inv_mem hp'
    show Induction.quotientMap P₁ (1⁻¹ * b') ∈ Wq
    rw [← hq]
    exact hhW
  rw [hWqeq] at hmem'
  obtain ⟨c, hcΩ, hc⟩ := hmem'
  have hc' : Induction.quotientMap P₁ (1⁻¹ * (c : H)) =
      Induction.quotientMap P₁ (1⁻¹ * b') := congrArg Subtype.val hc
  have hbc : b' * (c : H)⁻¹ ∈ P₁ := by
    have := QuotientGroup.rightRel_apply.mp (Quotient.exact hc')
    simpa using this
  have hbcQ : b' * (c : H)⁻¹ ∈ Q₂ := Q₂.mul_mem (hP₂Q₂ hb') (Q₂.inv_mem c.property)
  have hbcP : b' * (c : H)⁻¹ ∈ P₂ := hint ⟨hbc, hbcQ⟩
  apply hcΩ
  have := P₂.mul_mem (P₂.inv_mem hbcP) hb'
  simpa [mul_assoc] using this

end Abstract


section Nested

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]

/-- For nested represented parabolics `P = MN ⊂ Q = LU` with `P_L(F) = L(F) ∩ P(F)`, the
radical of `Q` lies in the radical of `P`: `U(F) ⊂ N(F)`. -/
theorem pointImage_radical_le_of_nested
    {G P M N Q L U PL NL : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G)
    {p : P ⟶ G} {m : M ⟶ P} {n : N ⟶ P} (hp : IsParabolicSubgroup p)
    (hm : IsRationalLeviSubgroup m) (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
    (hmul : IsIso (subgroupMultiplication m n))
    {q : Q ⟶ G} {l : L ⟶ Q} {uQ : U ⟶ Q} (hq : IsParabolicSubgroup q)
    (hl : IsRationalLeviSubgroup l) (huQ : LeviSubgroup.IsGeometricUnipotentRadical uQ)
    (hmulQ : IsIso (subgroupMultiplication l uQ))
    {pL : PL ⟶ L} {mL : M ⟶ PL} {nL : NL ⟶ PL} (hpL : IsParabolicSubgroup pL)
    (hmL : IsRationalLeviSubgroup mL) (hnL : LeviSubgroup.IsGeometricUnipotentRadical nL)
    (hmulL : IsIso (subgroupMultiplication mL nL))
    (hPQ : pointImage p ≤ pointImage q) (hM : mL ≫ pL ≫ l ≫ q = m ≫ p)
    (hPL : pointImage (pL ≫ l ≫ q) = pointImage (l ≫ q) ⊓ pointImage p) :
    pointImage (uQ ≫ q) ≤ pointImage (n ≫ p) := by
  have hnest := nestedParabolicPointDecomposition k G hG P M N Q L U PL NL
    p m n hp hm hn hmul q l uQ hq hl huQ hmulQ pL mL nL hpL hmL hnL hmulL hPQ hM hPL
  intro x hx
  have hx' : x ∈ ((pointImage (n ≫ p) : Set (rationalPoints G))) := by
    rw [hnest.2.1]
    exact ⟨1, Subgroup.one_mem _, x, hx, one_mul x⟩
  exact hx'

/-- For nested represented parabolics `P = MN ⊂ Q = LU` with `P_L(F) = L(F) ∩ P(F)`, every
point of `P(F)` is a product `y v` with `y ∈ P_L(F)` and `v ∈ U(F)`. -/
theorem exists_mul_of_mem_of_nested
    {G P M N Q L U PL NL : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G)
    {p : P ⟶ G} {m : M ⟶ P} {n : N ⟶ P} (hp : IsParabolicSubgroup p)
    (hm : IsRationalLeviSubgroup m) (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
    (hmul : IsIso (subgroupMultiplication m n))
    {q : Q ⟶ G} {l : L ⟶ Q} {uQ : U ⟶ Q} (hq : IsParabolicSubgroup q)
    (hl : IsRationalLeviSubgroup l) (huQ : LeviSubgroup.IsGeometricUnipotentRadical uQ)
    (hmulQ : IsIso (subgroupMultiplication l uQ))
    {pL : PL ⟶ L} {mL : M ⟶ PL} {nL : NL ⟶ PL} (hpL : IsParabolicSubgroup pL)
    (hmL : IsRationalLeviSubgroup mL) (hnL : LeviSubgroup.IsGeometricUnipotentRadical nL)
    (hmulL : IsIso (subgroupMultiplication mL nL))
    (hPQ : pointImage p ≤ pointImage q) (hM : mL ≫ pL ≫ l ≫ q = m ≫ p)
    (hPL : pointImage (pL ≫ l ≫ q) = pointImage (l ≫ q) ⊓ pointImage p)
    {x : rationalPoints G} (hx : x ∈ pointImage p) :
    ∃ y ∈ pointImage (pL ≫ l ≫ q), ∃ v ∈ pointImage (uQ ≫ q), y * v = x := by
  have hnest := nestedParabolicPointDecomposition k G hG P M N Q L U PL NL
    p m n hp hm hn hmul q l uQ hq hl huQ hmulQ pL mL nL hpL hmL hnL hmulL hPQ hM hPL
  have hx' : x ∈ ((pointImage p : Set (rationalPoints G))) := hx
  rw [hnest.2.2] at hx'
  obtain ⟨y, hy, v, hv, hyv⟩ := hx'
  exact ⟨y, hy, v, hv, hyv⟩

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k] in
/-- For represented parabolics `Q₁ = LU₁`, `Q₂ = LU₂` with the same embedded Levi `L`,
`U₁(F) ∩ Q₂(F) ⊂ U₂(F)`. -/
theorem radical_inf_parabolic_le_radical
    {G Q₁ U₁ Q₂ U₂ L : GroupScheme (Spec (CommRingCat.of k))} (hG : IsConnectedReductive G)
    {q₁ : Q₁ ⟶ G} {lQ₁ : L ⟶ Q₁} {rQ₁ : U₁ ⟶ Q₁} (hq₁ : IsParabolicSubgroup q₁)
    (hlQ₁ : IsRationalLeviSubgroup lQ₁) (hrQ₁ : LeviSubgroup.IsGeometricUnipotentRadical rQ₁)
    {q₂ : Q₂ ⟶ G} {lQ₂ : L ⟶ Q₂} {rQ₂ : U₂ ⟶ Q₂} (hq₂ : IsParabolicSubgroup q₂)
    (hlQ₂ : IsRationalLeviSubgroup lQ₂) (hrQ₂ : LeviSubgroup.IsGeometricUnipotentRadical rQ₂)
    (hlevQ₂ : lQ₂ ≫ q₂ = lQ₁ ≫ q₁) :
    pointImage (rQ₁ ≫ q₁) ⊓ pointImage q₂ ≤ pointImage (rQ₂ ≫ q₂) := by
  have := hG.isAffineHom
  have := hG.smooth
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨ξ, hPξ, hLξ⟩ := DynamicLeviConjugacy.exists_cocharacter_parabolic_levi parabolicDynamic
    dynamicGeometricUnipotentRadical hG hq₁ hlQ₁
  obtain ⟨ψ, hPψ, hLψ⟩ := DynamicLeviConjugacy.exists_cocharacter_parabolic_levi parabolicDynamic
    dynamicGeometricUnipotentRadical hG hq₂ hlQ₂
  have hU₁ := pointImage_radical_eq_dynamic dynamicGeometricUnipotentRadical hG ξ hq₁ hPξ hrQ₁
  have hU₂ := pointImage_radical_eq_dynamic dynamicGeometricUnipotentRadical hG ψ hq₂ hPψ hrQ₂
  have hQ₂pt : pointImage q₂ = (Dynamic.parabolic ψ).carrier (Over.mk (𝟙 _)) := by
    rw [pointImage_eq_range_carrier, hPψ]
  have hLψξ : Dynamic.centralizer ψ = Dynamic.centralizer ξ := by
    rw [← hLψ, ← hLξ, hlevQ₂]
  have hD := Dynamic.unipotent_inf_parabolic_eq_unipotent_inf_unipotent ξ ψ hLψξ.le
  rintro x ⟨hx₁, hx₂⟩
  rw [hU₁] at hx₁
  rw [hQ₂pt] at hx₂
  have h : x ∈ (Dynamic.unipotent ξ ⊓ Dynamic.parabolic ψ).carrier (Over.mk (𝟙 _)) :=
    ⟨hx₁, hx₂⟩
  rw [hD] at h
  rw [hU₂]
  exact h.2

end Nested

section OpenOrbit

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance outerSupportPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

/-- For represented parabolics `P` and `Q` of `G`, the orbit map `Q(F) → P(F)\P(F)Q(F)`,
`x ↦ P(F)x`, is open onto the orbit with the subspace topology of `P(F)\G(F)`. -/
theorem isOpenMap_parabolic_cosetOrbitMap (hG : IsConnectedReductive G)
    {P M Q L : GroupScheme (Spec (CommRingCat.of k))}
    {p : P ⟶ G} {l : M ⟶ P} (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    {q : Q ⟶ G} {lQ : L ⟶ Q} (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ) :
    IsOpenMap (Geometric.cosetOrbitMap (pointImage p) (pointImage q) 1) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : T2Space (rationalPoints G) :=
    Langlands.AlgebraicGeometry.PointTopology.rationalPoint_t2Space k G
  have : SecondCountableTopology (rationalPoints G) :=
    RationalPointFamily.reductiveRationalPoint_secondCountable k G hG
  have : SigmaCompactSpace (rationalPoints G) :=
    sigmaCompactSpace_of_locallyCompact_secondCountable
  have hfin := (representedParabolicDoubleCoset k G hG P M Q L p l hp hl q lQ hq hlQ).1
  have : Finite (DoubleCoset.Quotient (pointImage p : Set (rationalPoints G)) (pointImage q)) :=
    hfin
  obtain ⟨n, ⟨s⟩⟩ := Geometric.closedSubgroupOrbitOrdering (rationalPoints G)
    (pointImage p) (pointImage q) (isClosed_pointImage p hp.isClosedSubgroup)
      (isClosed_pointImage q hq.isClosedSubgroup) hfin
  have hloc := (Geometric.boundaryVanishingSupportPair (pointImage p) (pointImage q)
    s.bruhatLinearOrder s.isBruhatRefinement_bruhatLinearOrder 1).orbit_isLocallyClosed
  rw [inv_one] at hloc
  exact Geometric.isOpenMap_cosetOrbitMap _ _ _ (isClosed_pointImage p hp.isClosedSubgroup)
    (isClosed_pointImage q hq.isClosedSubgroup) hloc

end OpenOrbit

section Outer

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G M P₁ N₁ P₂ N₂ L Q₁ U₁ Q₂ U₂ P' N' : GroupScheme (Spec (CommRingCat.of k))}
  (hG : IsConnectedReductive G)
  {p₁ : P₁ ⟶ G} {l₁ : M ⟶ P₁} {r₁ : N₁ ⟶ P₁} (hp₁ : IsParabolicSubgroup p₁)
  (hl₁ : IsRationalLeviSubgroup l₁) (hr₁ : LeviSubgroup.IsGeometricUnipotentRadical r₁)
  (hmul₁ : IsIso (subgroupMultiplication l₁ r₁))
  {p₂ : P₂ ⟶ G} {l₂ : M ⟶ P₂} {r₂ : N₂ ⟶ P₂} (hp₂ : IsParabolicSubgroup p₂)
  (hl₂ : IsRationalLeviSubgroup l₂) (hr₂ : LeviSubgroup.IsGeometricUnipotentRadical r₂)
  (hmul₂ : IsIso (subgroupMultiplication l₂ r₂))
  {q₁ : Q₁ ⟶ G} {lQ₁ : L ⟶ Q₁} {rQ₁ : U₁ ⟶ Q₁} (hq₁ : IsParabolicSubgroup q₁)
  (hlQ₁ : IsRationalLeviSubgroup lQ₁) (hrQ₁ : LeviSubgroup.IsGeometricUnipotentRadical rQ₁)
  (hmulQ₁ : IsIso (subgroupMultiplication lQ₁ rQ₁))
  {q₂ : Q₂ ⟶ G} {lQ₂ : L ⟶ Q₂} {rQ₂ : U₂ ⟶ Q₂} (hq₂ : IsParabolicSubgroup q₂)
  (hlQ₂ : IsRationalLeviSubgroup lQ₂) (hrQ₂ : LeviSubgroup.IsGeometricUnipotentRadical rQ₂)
  (hmulQ₂ : IsIso (subgroupMultiplication lQ₂ rQ₂))
  {p' : P' ⟶ L} {l' : M ⟶ P'} {r' : N' ⟶ P'} (hp' : IsParabolicSubgroup p')
  (hl' : IsRationalLeviSubgroup l') (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
  (hmul' : IsIso (subgroupMultiplication l' r'))
  (hlev₂ : l₂ ≫ p₂ = l₁ ≫ p₁) (hlevQ₂ : lQ₂ ≫ q₂ = lQ₁ ≫ q₁)
  (hPQ₁ : pointImage p₁ ≤ pointImage q₁) (hPQ₂ : pointImage p₂ ≤ pointImage q₂)
  (hM : l' ≫ p' ≫ lQ₁ ≫ q₁ = l₁ ≫ p₁)
  (hP'₁ : pointImage (p' ≫ lQ₁ ≫ q₁) = pointImage p₁ ⊓ pointImage (lQ₁ ≫ q₁))
  (hP'₂ : pointImage (p' ≫ lQ₁ ≫ q₁) = pointImage p₂ ⊓ pointImage (lQ₁ ≫ q₁))

include hG hp₁ hl₁ hr₁ hmul₁ hq₁ hlQ₁ hrQ₁ hmulQ₁ hp' hl' hr' hmul' hPQ₁ hM hP'₁ in
/-- `U₁(F) ⊂ N₁(F)` for the nested pair `P₁ ⊂ Q₁`. -/
theorem outer_radical₁_le : pointImage (rQ₁ ≫ q₁) ≤ pointImage (r₁ ≫ p₁) :=
  pointImage_radical_le_of_nested hG hp₁ hl₁ hr₁ hmul₁ hq₁ hlQ₁ hrQ₁ hmulQ₁ hp' hl' hr' hmul'
    hPQ₁ hM (hP'₁.trans (inf_comm _ _))

include hG hp₂ hl₂ hr₂ hmul₂ hq₂ hlQ₂ hrQ₂ hmulQ₂ hp' hl' hr' hmul' hlev₂ hlevQ₂ hPQ₂ hM
  hP'₂ in
/-- `U₂(F) ⊂ N₂(F)` for the nested pair `P₂ ⊂ Q₂`. -/
theorem outer_radical₂_le : pointImage (rQ₂ ≫ q₂) ≤ pointImage (r₂ ≫ p₂) :=
  pointImage_radical_le_of_nested hG hp₂ hl₂ hr₂ hmul₂ hq₂ hlQ₂ hrQ₂ hmulQ₂ hp' hl' hr' hmul'
    hPQ₂ (by rw [hlevQ₂, hM, hlev₂]) (by rw [hlevQ₂]; exact hP'₂.trans (inf_comm _ _))

include hG hp₁ hl₁ hr₁ hmul₁ hp₂ hl₂ hr₂ hmul₂ hq₁ hlQ₁ hrQ₁ hmulQ₁ hq₂ hlQ₂ hrQ₂ hmulQ₂
  hp' hl' hr' hmul' hlev₂ hlevQ₂ hPQ₁ hPQ₂ hM hP'₁ hP'₂ in
/-- `P₁(F) ∩ Q₂(F) ⊂ P₂(F)`. -/
theorem outer_parabolic_inf_le : pointImage p₁ ⊓ pointImage q₂ ≤ pointImage p₂ := by
  rintro c ⟨hc₁, hc₂⟩
  obtain ⟨y, hy, v, hv, rfl⟩ := exists_mul_of_mem_of_nested hG hp₁ hl₁ hr₁ hmul₁ hq₁ hlQ₁ hrQ₁
    hmulQ₁ hp' hl' hr' hmul' hPQ₁ hM (hP'₁.trans (inf_comm _ _)) hc₁
  have hyP₂ : y ∈ pointImage p₂ := by
    rw [hP'₂] at hy
    exact hy.1
  have hvQ₂ : v ∈ pointImage q₂ := by
    have := (pointImage q₂).mul_mem ((pointImage q₂).inv_mem (hPQ₂ hyP₂)) hc₂
    rwa [inv_mul_cancel_left] at this
  have hvU₂ := radical_inf_parabolic_le_radical hG hq₁ hlQ₁ hrQ₁ hq₂ hlQ₂ hrQ₂ hlevQ₂
    ⟨hv, hvQ₂⟩
  have hvN₂ := outer_radical₂_le hG hp₂ hl₂ hr₂ hmul₂ hq₂ hlQ₂ hrQ₂ hmulQ₂ hp' hl' hr' hmul'
    hlev₂ hlevQ₂ hPQ₂ hM hP'₂ hvU₂
  exact (pointImage p₂).mul_mem hyP₂ (pointImage_comp_le p₂ r₂ hvN₂)

include hG hp₁ hl₁ hr₁ hmul₁ hq₁ hlQ₁ hrQ₁ hmulQ₁ hp' hl' hr' hmul' hlevQ₂ hPQ₁ hM hP'₁ in
/-- `Q₁(F) Q₂(F) = P₁(F) Q₂(F)`, read on double-coset classes of the identity. -/
theorem outer_doubleCoset_mk_eq_one {g : rationalPoints G}
    (hg : DoubleCoset.mk (pointImage q₁) (pointImage q₂) g =
      DoubleCoset.mk (pointImage q₁) (pointImage q₂) 1) :
    DoubleCoset.mk (pointImage p₁) (pointImage q₂) g =
      DoubleCoset.mk (pointImage p₁) (pointImage q₂) 1 := by
  obtain ⟨a, ha, b, hb, hgab⟩ := DoubleCoset.eq.mp hg.symm
  have hdec := isSemidirectDecomposition_pointImage q₁ lQ₁ rQ₁ hq₁.isClosedSubgroup hrQ₁
    hmulQ₁
  set y := hdec.projection ⟨a, ha⟩ with hy
  have hyu : ((y : rationalPoints G))⁻¹ * a ∈ pointImage (rQ₁ ≫ q₁) :=
    hdec.projection_inv_mul_mem ⟨a, ha⟩
  have hyQ₁ : (y : rationalPoints G) ∈ pointImage q₁ := hdec.levi_le y.2
  have hconj : a * (y : rationalPoints G)⁻¹ ∈ pointImage (rQ₁ ≫ q₁) := by
    have h := (Subgroup.mem_normalizer_iff.mp (hdec.le_normalizer hyQ₁) _).mp hyu
    simpa [mul_assoc] using h
  have hyQ₂ : (y : rationalPoints G) ∈ pointImage q₂ := by
    have h : (y : rationalPoints G) ∈ pointImage (lQ₂ ≫ q₂) := by
      rw [hlevQ₂]; exact y.2
    exact pointImage_comp_le q₂ lQ₂ h
  refine (DoubleCoset.eq.mpr ⟨a * (y : rationalPoints G)⁻¹,
    pointImage_comp_le p₁ r₁ (outer_radical₁_le hG hp₁ hl₁ hr₁ hmul₁ hq₁ hlQ₁ hrQ₁ hmulQ₁
      hp' hl' hr' hmul' hPQ₁ hM hP'₁ hconj),
    (y : rationalPoints G) * b, (pointImage q₂).mul_mem hyQ₂ hb, ?_⟩).symm
  rw [hgab]
  group

variable [IsAffineHom G.X.hom]

local instance outerBoundaryPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

include hG hp₁ hl₁ hr₁ hmul₁ hp₂ hl₂ hr₂ hmul₂ hq₁ hlQ₁ hrQ₁ hmulQ₁ hq₂ hlQ₂ hrQ₂ hmulQ₂
  hp' hl' hr' hmul' hlev₂ hlevQ₂ hPQ₁ hPQ₂ hM hP'₁ hP'₂ in
/-- The boundary of `P₁(F)P₂(F)` lies in the boundary of `Q₁(F)Q₂(F)`:
`closure (P₁P₂) \ P₁P₂ ⊆ closure (Q₁Q₂) \ Q₁Q₂`. -/
theorem outer_boundary_subset :
    closure (DoubleCoset.quotToDoubleCoset (pointImage p₁) (pointImage p₂)
        (DoubleCoset.mk (pointImage p₁) (pointImage p₂) 1)) \
      DoubleCoset.quotToDoubleCoset (pointImage p₁) (pointImage p₂)
        (DoubleCoset.mk (pointImage p₁) (pointImage p₂) 1) ⊆
    closure (DoubleCoset.quotToDoubleCoset (pointImage q₁) (pointImage q₂)
        (DoubleCoset.mk (pointImage q₁) (pointImage q₂) 1)) \
      DoubleCoset.quotToDoubleCoset (pointImage q₁) (pointImage q₂)
        (DoubleCoset.mk (pointImage q₁) (pointImage q₂) 1) := by
  rintro g ⟨hgcl, hgP⟩
  have hsub : DoubleCoset.quotToDoubleCoset (pointImage p₁) (pointImage p₂)
        (DoubleCoset.mk (pointImage p₁) (pointImage p₂) 1) ⊆
      DoubleCoset.quotToDoubleCoset (pointImage q₁) (pointImage q₂)
        (DoubleCoset.mk (pointImage q₁) (pointImage q₂) 1) := by
    intro h hh
    rw [DoubleCoset.mem_quotToDoubleCoset_iff] at hh ⊢
    obtain ⟨a, ha, b, hb, hab⟩ := DoubleCoset.eq.mp hh.symm
    exact (DoubleCoset.eq.mpr ⟨a, hPQ₁ ha, b, hPQ₂ hb, hab⟩).symm
  refine ⟨closure_mono hsub hgcl, ?_⟩
  intro hgQ
  apply hgP
  rw [DoubleCoset.mem_quotToDoubleCoset_iff] at hgQ ⊢
  have hgPQ := outer_doubleCoset_mk_eq_one hG hp₁ hl₁ hr₁ hmul₁ hq₁ hlQ₁ hrQ₁ hmulQ₁
    hp' hl' hr' hmul' hlevQ₂ hPQ₁ hM hP'₁ hgQ
  exact doubleCoset_mem_of_mem_closure (isClosed_pointImage p₂ hp₂.isClosedSubgroup) hPQ₂
    (outer_parabolic_inf_le hG hp₁ hl₁ hr₁ hmul₁ hp₂ hl₂ hr₂ hmul₂ hq₁ hlQ₁ hrQ₁ hmulQ₁
      hq₂ hlQ₂ hrQ₂ hmulQ₂ hp' hl' hr' hmul' hlev₂ hlevQ₂ hPQ₁ hPQ₂ hM hP'₁ hP'₂)
    (isOpenMap_parabolic_cosetOrbitMap hG hp₁ hl₁ hq₂ hlQ₂) hgcl hgPQ

end Outer

end Langlands.Aubert.General.RepresentedParabolic
