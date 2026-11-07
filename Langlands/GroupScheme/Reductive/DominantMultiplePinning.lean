import Langlands.GroupScheme.Reductive.DominantMultipleRealization
import Langlands.GroupScheme.Reductive.Pinning
import Langlands.GroupScheme.Rational.RootSignParabolicLie
import Langlands.GroupScheme.Dynamic.ConnectedProof
import Langlands.GroupScheme.Rational.RelativeTitsNondegeneracy
import Langlands.GroupScheme.Rational.RankOneParabolicMinimality
import Langlands.GroupScheme.Reductive.SteinbergBigCellGeometry
import Langlands.GroupScheme.Torus.UnipotentHom
import Langlands.GroupScheme.Rational.StandardLeviRootTransport
import Langlands.GroupScheme.MatrixRepresentationDual
import Langlands.GroupScheme.ClosedSubgroupMonomorphism
import Langlands.GroupScheme.AffineLinearEmbeddingProof

/-! # Realized characters from top weight lines for a split pinning -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.DominantMultiple

open AffineCoordinates

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] (p : SplitPinning G)

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

theorem pairing_eq (x : characterLattice p.torus) (y : cocharacterLattice p.torus) :
    p.rootDatum.toLinearMap x y = latticePairing p.torus x y := by
  rw [p.isRootDatum.1]

/-- Every root of a split pinning is a root of the supplied datum. -/
theorem exists_root_of_mem_relativeRoots {χ : characterLattice p.torus}
    (hχ : χ ∈ relativeRoots p.inclusion) : ∃ r, p.rootDatum.root r = χ := by
  rw [relativeRoots_eq_roots, ← p.isRootDatum.2.1] at hχ
  exact hχ

/-- A strictly dominant cocharacter has its dynamic parabolics inside those of every dominant
cocharacter. -/
theorem parabolic_le_of_dominant (nu mu : cocharacterLattice p.torus)
    (hnu : ∀ a ∈ p.base.support, 0 < latticePairing p.torus (p.rootDatum.root a) nu)
    (hmu : ∀ a ∈ p.base.support, 0 ≤ latticePairing p.torus (p.rootDatum.root a) mu) :
    Dynamic.parabolic (CommGroupScheme.groupHom nu ≫ p.inclusion) ≤
        Dynamic.parabolic (CommGroupScheme.groupHom mu ≫ p.inclusion) ∧
      Dynamic.parabolic (CommGroupScheme.groupHom (-nu) ≫ p.inclusion) ≤
        Dynamic.parabolic (CommGroupScheme.groupHom (-mu) ≫ p.inclusion) := by
  have : Smooth G.X.hom := p.isConnectedReductive.smooth
  have : ConnectedSpace G.X.left := p.isConnectedReductive.connectedSpace
  have hsign := Langlands.RootDatum.DominantMultiple.root_sign p.rootDatum p.base nu mu
    (fun a ha => by rw [pairing_eq]; exact hnu a ha)
    (fun a ha => by rw [pairing_eq]; exact hmu a ha)
  constructor
  · rw [RelativeRoot.parabolic_le_iff_nonnegative_rootSupport dynamicConnected p.isSplitTorus]
    intro χ hχ h0
    obtain ⟨r, rfl⟩ := exists_root_of_mem_relativeRoots p hχ
    rcases hsign r with ⟨_, h⟩ | ⟨h1, _⟩
    · rwa [pairing_eq] at h
    · rw [pairing_eq] at h1
      exact absurd h0 (not_le.mpr h1)
  · rw [RelativeRoot.parabolic_le_iff_nonnegative_rootSupport dynamicConnected p.isSplitTorus]
    intro χ hχ h0
    obtain ⟨r, rfl⟩ := exists_root_of_mem_relativeRoots p hχ
    rw [map_neg] at h0 ⊢
    rcases hsign r with ⟨h1, _⟩ | ⟨_, h⟩
    · rw [pairing_eq] at h1
      exact absurd h0 (not_le.mpr (neg_neg_of_pos h1))
    · rw [pairing_eq] at h
      exact neg_nonneg.mpr h

/-- A normalizing point for a root reflection fixes every cocharacter orthogonal to the root. -/
theorem cocharacter_comp_eq_of_pairing_eq_zero (mu : cocharacterLattice p.torus)
    (r : p.rootIndex) (hr : latticePairing p.torus (p.rootDatum.root r) mu = 0)
    (σ : p.torus ≅ p.torus) (hσ : characterAut σ = p.rootDatum.reflection r) :
    mu ≫ σ.hom = mu := by
  apply p.rootDatum.toLinearMap.flip.toPerfPair.injective
  apply LinearMap.ext
  intro x
  rw [LinearMap.toPerfPair_apply, LinearMap.toPerfPair_apply, LinearMap.flip_apply,
    LinearMap.flip_apply, pairing_eq, pairing_eq]
  have h := latticePairing_characterAut_cocharacterAut σ (p.rootDatum.reflection r x) mu
  rw [hσ, RootPairing.reflection_same, cocharacterAut_apply] at h
  rw [h, ← pairing_eq, ← pairing_eq, RootPairing.reflection_apply, map_sub, map_smul,
    LinearMap.sub_apply, LinearMap.smul_apply, pairing_eq p (p.rootDatum.root r), hr,
    smul_zero, sub_zero]

/-- A character of a group containing the dynamic parabolic of a cocharacter orthogonal to a
root is orthogonal to its coroot. -/
theorem pairing_coroot_eq_zero (mu : cocharacterLattice p.torus) (r : p.rootIndex)
    (hr : latticePairing p.torus (p.rootDatum.root r) mu = 0)
    {P : GroupScheme (Spec (CommRingCat.of k))} (iP : P ⟶ G)
    (hP : (Dynamic.parabolic (Dynamic.oppositeCocharacter
      (CommGroupScheme.groupHom mu ≫ p.inclusion))).IsRepresentedBy iP)
    (tP : p.torus.toGrp ⟶ P) (htP : tP ≫ iP = p.inclusion) (ψ : rationalCharacters P) :
    latticePairing p.torus
      (rationalCharacters.equivCharacterLattice p.torus (characterRestrict tP ψ))
      (p.rootDatum.coroot r) = 0 := by
  obtain ⟨n, σ, hn, hσ⟩ := p.isRootDatum.2.2 r
  have hmu := cocharacter_comp_eq_of_pairing_eq_zero p mu r hr σ hσ
  have hχ : (CommGroupScheme.groupHom mu ≫ p.inclusion) ≫ (G.innerIso n).hom =
      CommGroupScheme.groupHom mu ≫ p.inclusion := by
    rw [Category.assoc, hn, ← Category.assoc]
    change CommGroupScheme.groupHom (mu ≫ σ.hom) ≫ p.inclusion = _
    rw [hmu]
  have hcent := mem_centralizer_of_comp_innerIso _ n hχ
  rw [← Dynamic.centralizer_oppositeCocharacter] at hcent
  have hpar := Dynamic.centralizer_le_parabolic _ _ hcent
  rw [← hP.2] at hpar
  obtain ⟨n', hn'⟩ := SubgroupFunctor.mem_range.mp hpar
  have hfix := characterAut_characterRestrict_eq iP hP.1 tP p.inclusion htP n σ hn n' hn' ψ
  rw [hσ, RootPairing.reflection_apply, sub_eq_self] at hfix
  set x := rationalCharacters.equivCharacterLattice p.torus (characterRestrict tP ψ)
  have hc : p.rootDatum.coroot' r x = p.rootDatum.toLinearMap x (p.rootDatum.coroot r) := rfl
  rw [hc] at hfix
  have h2 := congrArg (fun m => p.rootDatum.toLinearMap m (p.rootDatum.coroot r)) hfix
  rw [map_smul, LinearMap.smul_apply, RootPairing.root_coroot_two, smul_eq_mul,
    map_zero, LinearMap.zero_apply] at h2
  rw [← pairing_eq]
  omega

/-- Characters of a unipotent group are trivial on points. -/
theorem characterEval_eq_one_of_isUnipotent {U Q : GroupScheme (Spec (CommRingCat.of k))}
    (hU : IsUnipotent U) (κ : U ⟶ Q) (T : Over (Spec (CommRingCat.of k))) (u : T ⟶ U.X)
    (ψ : rationalCharacters Q) : characterEval ψ T (u ≫ κ.hom.hom) = 1 := by
  rw [← characterEval_characterRestrict, characterEval_apply,
    hU.comp_eq_one_of_isSplitTorus isSplitTorus_gm _ T u, map_one]

variable {H U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]

/-- The top weight line of a representation diagonalized along a dominant cocharacter gives a
realized character, with the prescribed pairing and orthogonal to every coroot whose root is
orthogonal to the cocharacter. -/
theorem exists_mem_realizedSet_of_diagonal (nu : cocharacterLattice p.torus)
    (hnu : ∀ a ∈ p.base.support, 0 < latticePairing p.torus (p.rootDatum.root a) nu)
    (i : H ⟶ G) (hi : (Dynamic.parabolic (Dynamic.oppositeCocharacter
      (CommGroupScheme.groupHom nu ≫ p.inclusion))).IsRepresentedBy i)
    (tH : p.torus.toGrp ⟶ H) (htH : tH ≫ i = p.inclusion)
    (j : U ⟶ G) (hj : SubgroupFunctor.range j ≤
      Dynamic.unipotent (CommGroupScheme.groupHom nu ≫ p.inclusion)) (hU : IsUnipotent U)
    (mu : cocharacterLattice p.torus)
    (hmu : ∀ a ∈ p.base.support, 0 ≤ latticePairing p.torus (p.rootDatum.root a) mu)
    {N : ℕ} (ρ : MatrixRepresentation G (Fin N)) (e : Fin N → ℤ)
    (he : (CommGroupScheme.groupHom mu ≫ p.inclusion) ≫ ρ =
      GeneralLinear.diagonalCocharacter (Fin N) (CommRingCat.of k) e)
    (M : ℤ) (hM : ∀ a, e a ≤ M) :
    ∃ x ∈ realizedSet tH i j,
      latticePairing p.torus x mu = (Chevalley.topCard e M : ℤ) * M ∧
      ∀ r, latticePairing p.torus (p.rootDatum.root r) mu = 0 →
        latticePairing p.torus x (p.rootDatum.coroot r) = 0 := by
  let χ := CommGroupScheme.groupHom mu ≫ p.inclusion
  obtain ⟨hpos, hneg⟩ := parabolic_le_of_dominant p nu mu hnu hmu
  rw [groupHom_neg_comp_eq_oppositeCocharacter, groupHom_neg_comp_eq_oppositeCocharacter]
    at hneg
  let iP := Dynamic.Affine.parabolicHom (Dynamic.oppositeCocharacter χ)
  have hP : (Dynamic.parabolic (Dynamic.oppositeCocharacter χ)).IsRepresentedBy iP :=
    Dynamic.Affine.isRepresentedBy_parabolicHom _
  have : IsClosedImmersion iP.hom.hom.left := Dynamic.Affine.isClosedSubgroup_parabolicHom _
  have : IsAffineHom (Dynamic.Affine.parabolicScheme (Dynamic.oppositeCocharacter χ)).X.hom := by
    rw [← Over.w iP.hom.hom]
    infer_instance
  let iQ := Dynamic.Affine.parabolicHom χ
  have hQ : (Dynamic.parabolic χ).IsRepresentedBy iQ := Dynamic.Affine.isRepresentedBy_parabolicHom _
  have : IsClosedImmersion iQ.hom.hom.left := Dynamic.Affine.isClosedSubgroup_parabolicHom _
  have : IsAffineHom (Dynamic.Affine.parabolicScheme χ).X.hom := by
    rw [← Over.w iQ.hom.hom]
    infer_instance
  have hiP : SubgroupFunctor.range i ≤ Dynamic.parabolic (Dynamic.oppositeCocharacter χ) := by
    rw [hi.2]
    exact hneg
  have hjQ : SubgroupFunctor.range j ≤ Dynamic.parabolic χ :=
    hj.trans ((Dynamic.unipotent_le_parabolic _).trans hpos)
  let fP := hP.liftOfLE i hiP
  have hfP : fP ≫ iP = i := hP.liftOfLE_comp i hiP
  let κ := hQ.liftOfLE j hjQ
  have hκ : κ ≫ iQ = j := hQ.liftOfLE_comp j hjQ
  obtain ⟨ψ, f, hf1, hf2, hf3, heval⟩ := exists_topWeight_coefficient ρ χ e he M hM iP hP iQ hQ
    i fP hfP j κ hκ (fun T u ψ => characterEval_eq_one_of_isUnipotent hU κ T u ψ)
  refine ⟨rationalCharacters.equivCharacterLattice p.torus
    (characterRestrict tH (characterRestrict fP ψ)), ⟨_, f, rfl, hf1, hf2, hf3⟩, ?_, ?_⟩
  · apply latticePairing_eq_of_points
    intro V t
    have hx : (t ≫ (CommGroupScheme.groupHom mu).hom.hom ≫ tH.hom.hom ≫ fP.hom.hom) ≫
        iP.hom.hom = t ≫ χ.hom.hom := by
      simp only [Category.assoc, ← Grp.comp_hom_hom, hfP, htH]
      rfl
    rw [← heval V t _ hx]
    change Gm.pointsEquiv _ V (t ≫ (CommGroupScheme.groupHom mu).hom.hom ≫
      (tH ≫ fP ≫ ψ.toMul).hom.hom) = _
    rw [characterEval_apply]
    simp only [Grp.comp_hom_hom, Category.assoc]
  · intro r hr
    have h := pairing_coroot_eq_zero p mu r hr iP hP (tH ≫ fP)
      (by rw [Category.assoc, hfP, htH]) ψ
    rwa [characterRestrict_comp] at h

omit [IsAffineHom G.X.hom] in
/-- The dual of a representation diagonal along a cocharacter is diagonal with the negated
weights. -/
theorem comp_dual_eq_diagonalCocharacter {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation G n) (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (e : n → ℤ)
    (he : χ ≫ ρ = GeneralLinear.diagonalCocharacter n (CommRingCat.of k) e) :
    χ ≫ ρ.dual = GeneralLinear.diagonalCocharacter n (CommRingCat.of k) (-e) := by
  apply hom_ext_points
  intro V t
  apply (GeneralLinear.pointsEquiv n (CommRingCat.of k) V).injective
  have h1 : GeneralLinear.pointsEquiv n (CommRingCat.of k) V (t ≫ (χ ≫ ρ.dual).hom.hom) =
      ρ.dual.pointMatrix V (t ≫ χ.hom.hom) := by
    rw [MatrixRepresentation.pointMatrix_apply, Grp.comp_hom_hom, Category.assoc]
  have h2 : ρ.pointMatrix V (t ≫ χ.hom.hom) =
      GeneralLinear.diagonalUnits Γ(V.left, ⊤) e (Gm.pointsEquiv _ V t) := by
    rw [MatrixRepresentation.pointMatrix_apply, Category.assoc, ← Grp.comp_hom_hom, he,
      GeneralLinear.pointsEquiv_diagonalCocharacter]
  rw [h1, MatrixRepresentation.dual_pointMatrix, h2,
    GeneralLinear.pointsEquiv_diagonalCocharacter]
  apply Units.ext
  rw [GeneralLinear.matrixContragredient_coe, ← map_inv, GeneralLinear.coe_diagonalUnits,
    GeneralLinear.coe_diagonalUnits, Matrix.diagonal_transpose]
  congr 1
  funext a
  simp [inv_zpow', zpow_neg]

/-- If a faithful representation is trivial along a cocharacter, the cocharacter pairs
trivially with every character. -/
theorem latticePairing_eq_zero_of_diagonal_zero {n : Type} [Fintype n] [DecidableEq n]
    (mu : cocharacterLattice p.torus) (ρ : MatrixRepresentation G n) (hρ : Mono ρ.hom.hom)
    (e : n → ℤ)
    (he : (CommGroupScheme.groupHom mu ≫ p.inclusion) ≫ ρ =
      GeneralLinear.diagonalCocharacter n (CommRingCat.of k) e)
    (h0 : ∀ a, e a = 0) (y : characterLattice p.torus) :
    latticePairing p.torus y mu = 0 := by
  have hincl : Mono p.inclusion.hom.hom := p.isMaximalTorus.2.1.mono_overHom
  apply latticePairing_eq_of_points
  intro V t
  have ht : t ≫ (CommGroupScheme.groupHom mu).hom.hom = 1 := by
    apply (cancel_mono p.inclusion.hom.hom).mp
    apply (cancel_mono ρ.hom.hom).mp
    rw [MonObj.one_comp, MonObj.one_comp]
    apply (GeneralLinear.pointsEquiv n (CommRingCat.of k) V).injective
    have hc : ((t ≫ (CommGroupScheme.groupHom mu).hom.hom) ≫ p.inclusion.hom.hom) ≫
        ρ.hom.hom = t ≫ ((CommGroupScheme.groupHom mu ≫ p.inclusion) ≫ ρ).hom.hom := by
      simp only [Grp.comp_hom_hom, Category.assoc]
    rw [hc, he, GeneralLinear.pointsEquiv_diagonalCocharacter, map_one]
    apply Units.ext
    rw [GeneralLinear.coe_diagonalUnits]
    simp [h0]
  rw [← Category.assoc, ht, MonObj.one_comp, map_one, zpow_zero]

/-- A cocharacter pairing nontrivially with some character is diagonal, with a positive largest
weight, in some actual matrix representation. -/
theorem exists_diagonal_pos (mu : cocharacterLattice p.torus)
    (hne : ∃ y : characterLattice p.torus, latticePairing p.torus y mu ≠ 0) :
    ∃ (N : ℕ) (ρ : MatrixRepresentation G (Fin N)) (e : Fin N → ℤ) (a₀ : Fin N),
      (CommGroupScheme.groupHom mu ≫ p.inclusion) ≫ ρ =
        GeneralLinear.diagonalCocharacter (Fin N) (CommRingCat.of k) e ∧
      (∀ a, e a ≤ e a₀) ∧ 0 < e a₀ := by
  classical
  have : Smooth G.X.hom := p.isConnectedReductive.smooth
  obtain ⟨N, ρ₀, hρ₀⟩ := affineLinearEmbeddingStatement k G inferInstance inferInstance
  let χ := CommGroupScheme.groupHom mu ≫ p.inclusion
  obtain ⟨g, e, hg⟩ := GeneralLinear.exists_innerIso_comp_eq_diagonalCocharacter k (χ ≫ ρ₀)
  let ρ₁ : MatrixRepresentation G (Fin N) :=
    ρ₀ ≫ ((GeneralLinear.groupScheme (Fin N) (CommRingCat.of k)).innerIso g).hom
  have he₁ : χ ≫ ρ₁ = GeneralLinear.diagonalCocharacter (Fin N) (CommRingCat.of k) e := by
    rw [← hg]
    simp only [χ, ρ₁, Category.assoc]
  have hmono₀ : Mono ρ₀.hom.hom := hρ₀.mono_overHom
  have hmono₁ : Mono ρ₁.hom.hom := by
    change Mono (ρ₀.hom.hom ≫
      ((GeneralLinear.groupScheme (Fin N) (CommRingCat.of k)).innerIso g).hom.hom.hom)
    infer_instance
  have hnz : ∃ a, e a ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨y, hy⟩ := hne
    exact hy (latticePairing_eq_zero_of_diagonal_zero p mu ρ₁ hmono₁ e he₁ h y)
  obtain ⟨ρ, e', he', a, ha⟩ : ∃ (ρ : MatrixRepresentation G (Fin N)) (e' : Fin N → ℤ),
      χ ≫ ρ = GeneralLinear.diagonalCocharacter (Fin N) (CommRingCat.of k) e' ∧
        ∃ a, 0 < e' a := by
    obtain ⟨a, ha⟩ := hnz
    rcases lt_or_gt_of_ne ha with h | h
    · exact ⟨ρ₁.dual, -e, comp_dual_eq_diagonalCocharacter ρ₁ χ e he₁, a, by simpa using h⟩
    · exact ⟨ρ₁, e, he₁, a, h⟩
  have : Nonempty (Fin N) := ⟨a⟩
  obtain ⟨a₀, ha₀⟩ := Finite.exists_max e'
  exact ⟨N, ρ, e', a₀, he', ha₀, ha.trans_le (ha₀ a)⟩

/-- A dominant cocharacter pairing nontrivially with some character gives a realized character
pairing positively with it. -/
theorem exists_mem_realizedSet_pos (nu : cocharacterLattice p.torus)
    (hnu : ∀ a ∈ p.base.support, 0 < latticePairing p.torus (p.rootDatum.root a) nu)
    (i : H ⟶ G) (hi : (Dynamic.parabolic (Dynamic.oppositeCocharacter
      (CommGroupScheme.groupHom nu ≫ p.inclusion))).IsRepresentedBy i)
    (tH : p.torus.toGrp ⟶ H) (htH : tH ≫ i = p.inclusion)
    (j : U ⟶ G) (hj : SubgroupFunctor.range j ≤
      Dynamic.unipotent (CommGroupScheme.groupHom nu ≫ p.inclusion)) (hU : IsUnipotent U)
    (mu : cocharacterLattice p.torus)
    (hmu : ∀ a ∈ p.base.support, 0 ≤ latticePairing p.torus (p.rootDatum.root a) mu)
    (hne : ∃ y : characterLattice p.torus, latticePairing p.torus y mu ≠ 0) :
    ∃ x ∈ realizedSet tH i j, 0 < latticePairing p.torus x mu ∧
      ∀ r, latticePairing p.torus (p.rootDatum.root r) mu = 0 →
        latticePairing p.torus x (p.rootDatum.coroot r) = 0 := by
  obtain ⟨N, ρ, e, a₀, he, ha₀, hpos⟩ := exists_diagonal_pos p mu hne
  obtain ⟨x, hx, hpair, horth⟩ := exists_mem_realizedSet_of_diagonal p nu hnu i hi tH htH j hj
    hU mu hmu ρ e he (e a₀) ha₀
  refine ⟨x, hx, ?_, horth⟩
  rw [hpair]
  have hcard : 0 < Chevalley.topCard e (e a₀) :=
    Finset.card_pos.mpr ⟨a₀, Chevalley.mem_topSet.mpr rfl⟩
  positivity

/-- For a cocharacter orthogonal to every root, the top weight line is a character of the
whole group, so both it and its negative are realized. -/
theorem exists_neg_mem_realizedSet_of_central (i : H ⟶ G) (tH : p.torus.toGrp ⟶ H)
    (htH : tH ≫ i = p.inclusion) (j : U ⟶ G) (hU : IsUnipotent U)
    (mu : cocharacterLattice p.torus)
    (hmu : ∀ r, latticePairing p.torus (p.rootDatum.root r) mu = 0)
    (hne : ∃ y : characterLattice p.torus, latticePairing p.torus y mu ≠ 0) :
    ∃ x ∈ realizedSet tH i j, -x ∈ realizedSet tH i j ∧ 0 < latticePairing p.torus x mu ∧
      ∀ r, latticePairing p.torus x (p.rootDatum.coroot r) = 0 := by
  have : Smooth G.X.hom := p.isConnectedReductive.smooth
  have : ConnectedSpace G.X.left := p.isConnectedReductive.connectedSpace
  obtain ⟨N, ρ, e, a₀, he, ha₀, hpos⟩ := exists_diagonal_pos p mu hne
  let χ := CommGroupScheme.groupHom mu ≫ p.inclusion
  have hroots : ∀ (ζ : cocharacterLattice p.torus), (ζ = mu ∨ ζ = -mu) →
      Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ p.inclusion) = ⊤ := by
    intro ζ hζ
    apply Dynamic.parabolic_eq_top_of_nonnegative_relativeRoots p.isSplitTorus
    intro α hα
    obtain ⟨r, rfl⟩ := exists_root_of_mem_relativeRoots p hα
    rcases hζ with rfl | rfl
    · rw [hmu r]
    · rw [map_neg, hmu r, neg_zero]
  have hP : (Dynamic.parabolic (Dynamic.oppositeCocharacter χ)).IsRepresentedBy (𝟙 G) := by
    rw [← groupHom_neg_comp_eq_oppositeCocharacter, hroots (-mu) (Or.inr rfl)]
    exact SubgroupFunctor.top_isRepresentedBy_id G
  have hQ : (Dynamic.parabolic χ).IsRepresentedBy (𝟙 G) := by
    rw [hroots mu (Or.inl rfl)]
    exact SubgroupFunctor.top_isRepresentedBy_id G
  obtain ⟨ψ, f, hf1, hf2, hf3, heval⟩ := exists_topWeight_coefficient ρ χ e he (e a₀) ha₀
    (𝟙 G) hP (𝟙 G) hQ i i (Category.comp_id i) j j (Category.comp_id j)
    (fun T u ψ => characterEval_eq_one_of_isUnipotent hU j T u ψ)
  have hres : ∀ φ : rationalCharacters G,
      rationalCharacters.equivCharacterLattice p.torus (characterRestrict tH
        (characterRestrict i φ)) =
      rationalCharacters.equivCharacterLattice p.torus (characterRestrict p.inclusion φ) := by
    intro φ
    rw [← htH, characterRestrict_comp]
    rfl
  refine ⟨rationalCharacters.equivCharacterLattice p.torus (characterRestrict tH
    (characterRestrict i ψ)), ⟨_, f, rfl, hf1, hf2, hf3⟩, ?_, ?_, ?_⟩
  · refine ⟨characterRestrict i (-ψ), characterCoordinate G (-ψ), ?_,
      isRealizedCoordinate_characterCoordinate i j (-ψ)
        (fun T u => characterEval_eq_one_of_isUnipotent hU j T u (-ψ))⟩
    rw [map_neg, map_neg, map_neg]
  · have hpair : latticePairing p.torus (rationalCharacters.equivCharacterLattice p.torus
        (characterRestrict tH (characterRestrict i ψ))) mu =
        (Chevalley.topCard e (e a₀) : ℤ) * e a₀ := by
      apply latticePairing_eq_of_points
      intro V t
      have hx : (t ≫ (CommGroupScheme.groupHom mu).hom.hom ≫ tH.hom.hom ≫ i.hom.hom) ≫
          (𝟙 G : G ⟶ G).hom.hom = t ≫ χ.hom.hom := by
        simp only [Category.assoc, ← Grp.comp_hom_hom, htH]
        rfl
      rw [← heval V t _ hx]
      change Gm.pointsEquiv _ V (t ≫ (CommGroupScheme.groupHom mu).hom.hom ≫
        (tH ≫ i ≫ ψ.toMul).hom.hom) = _
      rw [characterEval_apply]
      simp only [Grp.comp_hom_hom, Category.assoc]
    rw [hpair]
    have hcard : 0 < Chevalley.topCard e (e a₀) :=
      Finset.card_pos.mpr ⟨a₀, Chevalley.mem_topSet.mpr rfl⟩
    positivity
  · intro r
    have h := pairing_coroot_eq_zero p mu r (hmu r) (𝟙 G) hP (tH ≫ i)
      (by rw [Category.comp_id, htH]) ψ
    rwa [characterRestrict_comp] at h

end Langlands.GroupScheme.DominantMultiple
