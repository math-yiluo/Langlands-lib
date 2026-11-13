import Langlands.Representation.Intertwining.PQCompositionBruhatOrder
import Langlands.GroupScheme.Rational.RootSignParabolicLie
import Langlands.GroupScheme.Rational.RootSignUnipotentLie
import Langlands.GroupScheme.Rational.CentralizerRootSupport
import Langlands.GroupScheme.Rational.MaximalTorusParameterExistenceProof
import Langlands.GroupScheme.Dynamic.ConnectedProof
import Langlands.GroupScheme.Rational.PointDecomposition
import Langlands.GroupScheme.Rational.StandardRestrictedConjugation
import Langlands.Representation.Aubert.General.DynamicInductionExactness

/-! # Renard VII.3.5 (i): `M ∩ zP₂z⁻¹ = M ∩ zP₃z⁻¹` through the rank-one Levi `L` -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry Topology Filter Pointwise
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

section Orbit

variable {S : Scheme.{u}} {T : CommGroupScheme S} {G : GroupScheme S}
  (i : T.toGrp ⟶ G) (ν ζ : cocharacterLattice T)

/-- On points centralizing `ζ`, adding a multiple of `ζ` does not change the orbit. -/
theorem orbit_add_nsmul_of_mem_centralizer (n : ℕ) {U : Over S} {g : U ⟶ G.X}
    (hg : g ∈ (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).carrier U) :
    Dynamic.orbit (CommGroupScheme.groupHom (ν + n • ζ) ≫ i) g =
      Dynamic.orbit (CommGroupScheme.groupHom ν ≫ i) g := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [succ_nsmul, ← add_assoc, Dynamic.orbit_add_of_mem_centralizer i (ν + n • ζ) ζ g hg, ih]

/-- On points centralizing `ζ`, the parabolics of `ν` and `ν + n ζ` agree. -/
theorem mem_parabolic_add_nsmul_iff (n : ℕ) {U : Over S} {g : U ⟶ G.X}
    (hg : g ∈ (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).carrier U) :
    g ∈ (Dynamic.parabolic (CommGroupScheme.groupHom (ν + n • ζ) ≫ i)).carrier U ↔
      g ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier U := by
  simp only [Dynamic.mem_parabolic, Dynamic.IsOrbitExtension,
    orbit_add_nsmul_of_mem_centralizer i ν ζ n hg]

/-- On points centralizing `ζ`, the identity-limit subgroups of `ν` and `ν + n ζ` agree. -/
theorem mem_unipotent_add_nsmul_iff (n : ℕ) {U : Over S} {g : U ⟶ G.X}
    (hg : g ∈ (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).carrier U) :
    g ∈ (Dynamic.unipotent (CommGroupScheme.groupHom (ν + n • ζ) ≫ i)).carrier U ↔
      g ∈ (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier U := by
  simp only [Dynamic.mem_unipotent, Dynamic.HasLimit, Dynamic.IsOrbitExtension,
    orbit_add_nsmul_of_mem_centralizer i ν ζ n hg]

end Orbit

section LeviPoint

open BruhatTits.DynamicUnipotentContainment

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [T2Space F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom]

/-- A rational point `z` of the dynamic parabolic `P(χ)` such that `z⁻¹ χ(s) z ∈ Z(χ)(F)` for
every `s` lies in `Z(χ)(F)`: in `z = l u`, the radical part `u` commutes with every `χ(s)`. -/
theorem mem_levi_of_mem_parabolic_of_conj
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) {z : rationalPoints G}
    (hz : z ∈ RationalPoint.parabolic χ)
    (hconj : ∀ s : Fˣ, z⁻¹ * cocharPoint χ s * z ∈ RationalPoint.levi χ) :
    z ∈ RationalPoint.levi χ := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨⟨l, u⟩, ⟨hl, hu, rfl⟩, -⟩ := RationalPoint.existsUnique_levi_mul_unipotent χ hz
  have hu1 : u = 1 := by
    apply eq_one_of_mem_unipotentPoints_of_commute χ hu
    intro s
    refine commute_of_commutator_eq_one (N := RationalPoint.unipotent χ)
      (RationalPoint.levi_le_normalizer_unipotent χ (cocharPoint_mem_centralizer χ s)) hu
      fun hmem => ?_
    have hcomm : Commute l (cocharPoint χ s) := commute_cocharPoint χ hl s
    have hx' : l⁻¹ * cocharPoint χ s * l = cocharPoint χ s := by
      rw [mul_assoc, ← hcomm.eq, inv_mul_cancel_left]
    have heq : u⁻¹ * cocharPoint χ s * u = (l * u)⁻¹ * cocharPoint χ s * (l * u) := by
      rw [show (l * u)⁻¹ * cocharPoint χ s * (l * u) =
        u⁻¹ * (l⁻¹ * cocharPoint χ s * l) * u by group, hx']
    have hL : (cocharPoint χ s)⁻¹ * (u⁻¹ * cocharPoint χ s * u) ∈ RationalPoint.levi χ := by
      rw [heq]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (cocharPoint_mem_centralizer χ s))
        (hconj s)
    have h := (RationalPoint.levi_inf_unipotent χ).le ⟨hL, hmem⟩
    exact Subgroup.mem_bot.mp h
  rw [hu1, mul_one]
  exact hl

end LeviPoint

section Cocharacter

variable {k : Type u} [Field k] {G M P N Pb Nb : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]

/-- Scheme-level cocharacter data for one represented parabolic `P = MN` and an opposite
`P̄ = MN̄`, read on a split component `a` of `M`: a cocharacter `λ` of `A` with
`roots(N) = {λ > 0}`, `roots(N̄) = {λ < 0}`, `P = P(λ)`, `N = U(λ)`, `M = Z(λ)` as subgroup
functors, `⟨β, λ⟩ ≠ 0` for every root `β`, and the roots are stable under negation. -/
theorem exists_dynamic_oppositePair_cocharacter (hG : IsConnectedReductive G)
    {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}
    (ha : IsSplitComponent a) {m₀ : M ⟶ G}
    {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P} (hp : IsParabolicSubgroup p)
    (hl : IsRationalLeviSubgroup l) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    {pb : Pb ⟶ G} {lb : M ⟶ Pb} {rb : Nb ⟶ Pb} (hpb : IsParabolicSubgroup pb)
    (hlb : IsRationalLeviSubgroup lb) (hrb : LeviSubgroup.IsGeometricUnipotentRadical rb)
    (hm : l ≫ p = m₀) (hmb : lb ≫ pb = m₀)
    (hpts : pointImage p ⊓ pointImage pb = pointImage m₀) :
    ∃ lam : cocharacterLattice A,
      RelativeRoot.subgroupRelativeRoots (a ≫ m₀) (SubgroupFunctor.range (r ≫ p)) =
          positiveRelativeRoots (a ≫ m₀) lam ∧
      RelativeRoot.subgroupRelativeRoots (a ≫ m₀) (SubgroupFunctor.range (rb ≫ pb)) =
          positiveRelativeRoots (a ≫ m₀) (-lam) ∧
      SubgroupFunctor.range p =
          Dynamic.parabolic (CommGroupScheme.groupHom lam ≫ a ≫ m₀) ∧
      SubgroupFunctor.range (r ≫ p) =
          Dynamic.unipotent (CommGroupScheme.groupHom lam ≫ a ≫ m₀) ∧
      SubgroupFunctor.range m₀ =
          Dynamic.centralizer (CommGroupScheme.groupHom lam ≫ a ≫ m₀) ∧
      (∀ β ∈ relativeRoots (a ≫ m₀), latticePairing A β lam ≠ 0) ∧
      (∀ β ∈ relativeRoots (a ≫ m₀), -β ∈ relativeRoots (a ≫ m₀)) := by
  subst hm
  have : Smooth G.X.hom := hG.smooth
  obtain ⟨R⟩ := parabolicRootPresentationExistence k G hG P M A p l a hp hl ha
  obtain ⟨S⟩ := parabolicRootPresentationExistence k G hG Pb M A pb lb a hpb hlb ha
  have hpoints : (SubgroupFunctor.range p).carrier (Over.mk (𝟙 _)) ⊓
      (SubgroupFunctor.range pb).carrier (Over.mk (𝟙 _)) =
      (SubgroupFunctor.range (l ≫ p)).carrier (Over.mk (𝟙 _)) := by
    simpa only [pointImage_eq_range_carrier] using hpts
  have hsigns := R.opposite_componentRoot_signs S hG hmb hpoints
  refine ⟨R.splitComponentCocharacter, R.subgroupRelativeRoots_radical hr, ?_,
    R.parabolic_eq_splitComponentCocharacter, R.range_comp_radical_eq hr,
    R.levi_eq_splitComponentCocharacter, ?_,
    fun β hβ => R.neg_mem_componentRelativeRoots hG hβ⟩
  · have h := S.subgroupRelativeRoots_radical hrb
    rw [hmb] at h
    rw [h]
    ext β
    simp only [positiveRelativeRoots, Set.mem_ofPred_eq, latticePairing_neg_right, neg_pos]
    exact ⟨fun h => ⟨h.1, (hsigns β h.1).2.mp h.2⟩, fun h => ⟨h.1, (hsigns β h.1).2.mpr h.2⟩⟩
  · intro β hβ hzero
    have : IsAffineHom M.X.hom := hl.isConnectedReductive.isAffineHom
    have : Smooth M.X.hom := hl.isConnectedReductive.smooth
    have := (hl.isClosedSubgroup.comp hp.isClosedSubgroup).mono
    have hfac := relativeRoots_centralizer_factor dynamicLie (a ≫ l ≫ p) a (l ≫ p) rfl
      R.splitComponentCocharacter
      ⟨Over.mono_of_mono_left _, R.levi_eq_splitComponentCocharacter⟩
    have hβa : β ∈ relativeRoots a := by
      rw [hfac]
      exact ⟨hβ, hzero⟩
    have hc : IsCentral (CommGroupScheme.groupHom (𝟙 A) ≫ a) := by
      change IsCentral (𝟙 A.toGrp ≫ a)
      rw [Category.id_comp]
      exact ha.1.2
    have hz := root_restrict_eq_zero_of_isCentral a (𝟙 A) ha.1.1.1 hc hβa
    exact (mem_relativeRoots.mp hβa).1 (by simpa using hz)

end Cocharacter

set_option maxHeartbeats 4000000 in
/-- Renard VII.3.5 (i), printed p.238: for `z` with `P₁zP₂ <_{P₁P₂} P₁P₂` such that `M ∩ zMz⁻¹`
contains a maximal split torus of `G`, `M ∩ zP₂z⁻¹ = M ∩ zP₃z⁻¹` and `M ∩ zN₂z⁻¹ = M ∩ zN₃z⁻¹`.
The Levi `L = Z(μ)` of Renard is the centralizer of `μ = c₂ λ₁ + c₁ λ₂`, where `α` is the
root of `N₁ ∩ N̄₂`, `c₁ = ⟨α, λ₁⟩` and `c₂ = -⟨α, λ₂⟩`. -/
theorem pqCompositionLeviIntersection :
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (M P₁ N₁ P₂ N₂ P₃ N₃ Pb₁ Nb₁ Pb₂ Nb₂ Pb₃ Nb₃ : GroupScheme (Spec (CommRingCat.of k)))
      (p₁ : P₁ ⟶ G) (l₁ : M ⟶ P₁) (r₁ : N₁ ⟶ P₁)
      (_hp₁ : IsParabolicSubgroup p₁) (_hl₁ : IsRationalLeviSubgroup l₁)
      (_hr₁ : LeviSubgroup.IsGeometricUnipotentRadical r₁)
      (_hmul₁ : IsIso (subgroupMultiplication l₁ r₁))
      (p₂ : P₂ ⟶ G) (l₂ : M ⟶ P₂) (r₂ : N₂ ⟶ P₂)
      (_hp₂ : IsParabolicSubgroup p₂) (_hl₂ : IsRationalLeviSubgroup l₂)
      (_hr₂ : LeviSubgroup.IsGeometricUnipotentRadical r₂)
      (_hmul₂ : IsIso (subgroupMultiplication l₂ r₂))
      (p₃ : P₃ ⟶ G) (l₃ : M ⟶ P₃) (r₃ : N₃ ⟶ P₃)
      (_hp₃ : IsParabolicSubgroup p₃) (_hl₃ : IsRationalLeviSubgroup l₃)
      (_hr₃ : LeviSubgroup.IsGeometricUnipotentRadical r₃)
      (_hmul₃ : IsIso (subgroupMultiplication l₃ r₃))
      (pb₁ : Pb₁ ⟶ G) (lb₁ : M ⟶ Pb₁) (rb₁ : Nb₁ ⟶ Pb₁)
      (_hpb₁ : IsParabolicSubgroup pb₁) (_hlb₁ : IsRationalLeviSubgroup lb₁)
      (_hrb₁ : LeviSubgroup.IsGeometricUnipotentRadical rb₁)
      (_hmulb₁ : IsIso (subgroupMultiplication lb₁ rb₁))
      (pb₂ : Pb₂ ⟶ G) (lb₂ : M ⟶ Pb₂) (rb₂ : Nb₂ ⟶ Pb₂)
      (_hpb₂ : IsParabolicSubgroup pb₂) (_hlb₂ : IsRationalLeviSubgroup lb₂)
      (_hrb₂ : LeviSubgroup.IsGeometricUnipotentRadical rb₂)
      (_hmulb₂ : IsIso (subgroupMultiplication lb₂ rb₂))
      (pb₃ : Pb₃ ⟶ G) (lb₃ : M ⟶ Pb₃) (rb₃ : Nb₃ ⟶ Pb₃)
      (_hpb₃ : IsParabolicSubgroup pb₃) (_hlb₃ : IsRationalLeviSubgroup lb₃)
      (_hrb₃ : LeviSubgroup.IsGeometricUnipotentRadical rb₃)
      (_hmulb₃ : IsIso (subgroupMultiplication lb₃ rb₃)),
      l₂ ≫ p₂ = l₁ ≫ p₁ → l₃ ≫ p₃ = l₁ ≫ p₁ →
      lb₁ ≫ pb₁ = l₁ ≫ p₁ → lb₂ ≫ pb₂ = l₁ ≫ p₁ → lb₃ ≫ pb₃ = l₁ ≫ p₁ →
      pointImage p₁ ⊓ pointImage pb₁ = pointImage (l₁ ≫ p₁) →
      pointImage p₂ ⊓ pointImage pb₂ = pointImage (l₁ ≫ p₁) →
      pointImage p₃ ⊓ pointImage pb₃ = pointImage (l₁ ≫ p₁) →
      ∀ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ M),
        IsSplitComponent a →
        let rootsIn : SubgroupFunctor G → Set (characterLattice A) := fun F =>
          RelativeRoot.subgroupRelativeRoots (a ≫ l₁ ≫ p₁) F ∩
            RelativeRoot.indivisibleRoots (a ≫ l₁ ≫ p₁)
        let d : SubgroupFunctor G → SubgroupFunctor G → ℕ := fun F F' =>
          (rootsIn F ∩ rootsIn F').ncard
        d (SubgroupFunctor.range (r₁ ≫ p₁)) (SubgroupFunctor.range (rb₂ ≫ pb₂)) +
            d (SubgroupFunctor.range (r₂ ≫ p₂)) (SubgroupFunctor.range (rb₃ ≫ pb₃)) =
          d (SubgroupFunctor.range (r₁ ≫ p₁)) (SubgroupFunctor.range (rb₃ ≫ pb₃)) →
        d (SubgroupFunctor.range (r₁ ≫ p₁)) (SubgroupFunctor.range (rb₂ ≫ pb₂)) = 1 →
        ∀ (z : rationalPoints G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
          (i : T.toGrp ⟶ G), IsMaximalSplitTorus i →
          ∀ ta : T.toGrp ⟶ M, ta ≫ l₁ ≫ p₁ = i →
          ∀ tb : T.toGrp ⟶ M, tb ≫ l₁ ≫ p₁ ≫ (G.innerIso z).hom = i →
          Geometric.BruhatLT (pointImage p₁) (pointImage p₂)
              (DoubleCoset.mk (pointImage p₁) (pointImage p₂) z)
              (identityParabolicDoubleCoset p₁ p₂) →
            SubgroupFunctor.range (l₁ ≫ p₁) ⊓
                SubgroupFunctor.range (p₂ ≫ (G.innerIso z).hom) =
              SubgroupFunctor.range (l₁ ≫ p₁) ⊓
                SubgroupFunctor.range (p₃ ≫ (G.innerIso z).hom) ∧
            SubgroupFunctor.range (l₁ ≫ p₁) ⊓
                SubgroupFunctor.range (r₂ ≫ p₂ ≫ (G.innerIso z).hom) =
              SubgroupFunctor.range (l₁ ≫ p₁) ⊓
                SubgroupFunctor.range (r₃ ≫ p₃ ≫ (G.innerIso z).hom)
    := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ M P₁ N₁ P₂ N₂ P₃ N₃ Pb₁ Nb₁ Pb₂ Nb₂ Pb₃ Nb₃ p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁
    p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂ p₃ l₃ r₃ hp₃ hl₃ hr₃ hmul₃
    pb₁ lb₁ rb₁ hpb₁ hlb₁ hrb₁ hmulb₁ pb₂ lb₂ rb₂ hpb₂ hlb₂ hrb₂ hmulb₂
    pb₃ lb₃ rb₃ hpb₃ hlb₃ hrb₃ hmulb₃ h21 h31 hb1 hb2 hb3 ho1 ho2 ho3 A a ha rootsIn d hd hd1
    z T i hi ta hta tb htb hz
  have : Smooth G.X.hom := hG.smooth
  have : ConnectedSpace G.X.left := hG.connectedSpace
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsSeparated G.X.hom := hG.isSeparated
  have : IsAffineHom M.X.hom := hl₁.isConnectedReductive.isAffineHom
  have hS : IsSplitTorus A.toGrp := ha.1.1.1
  obtain ⟨lam₁, hR₁, -, hP₁, -, -, h0₁, hneg⟩ :=
    exists_dynamic_oppositePair_cocharacter hG ha hp₁ hl₁ hr₁ hpb₁ hlb₁ hrb₁ rfl hb1 ho1
  obtain ⟨lam₂, hR₂, hRb₂, hP₂, hN₂, -, h0₂, -⟩ :=
    exists_dynamic_oppositePair_cocharacter hG ha hp₂ hl₂ hr₂ hpb₂ hlb₂ hrb₂ h21 hb2 ho2
  obtain ⟨lam₃, -, hRb₃, hP₃, hN₃, -, h0₃, -⟩ :=
    exists_dynamic_oppositePair_cocharacter hG ha hp₃ hl₃ hr₃ hpb₃ hlb₃ hrb₃ h31 hb3 ho3
  -- The root-distance hypotheses in terms of the three cocharacters.
  dsimp only [d, rootsIn] at hd hd1
  rw [hR₁, hR₂, hRb₂, hRb₃] at hd
  rw [hR₁, hRb₂] at hd1
  set I := RelativeRoot.indivisibleRoots (a ≫ l₁ ≫ p₁) with hI
  have hfin : (relativeRoots (a ≫ l₁ ≫ p₁)).Finite := hS.finite_relativeRoots _
  have hcover : (positiveRelativeRoots (a ≫ l₁ ≫ p₁) lam₁ ∩ I) ∩
      (positiveRelativeRoots (a ≫ l₁ ≫ p₁) (-lam₃) ∩ I) ⊆
      ((positiveRelativeRoots (a ≫ l₁ ≫ p₁) lam₁ ∩ I) ∩
        (positiveRelativeRoots (a ≫ l₁ ≫ p₁) (-lam₂) ∩ I)) ∪
      ((positiveRelativeRoots (a ≫ l₁ ≫ p₁) lam₂ ∩ I) ∩
        (positiveRelativeRoots (a ≫ l₁ ≫ p₁) (-lam₃) ∩ I)) := by
    rintro β ⟨⟨⟨hβ, h1⟩, hβI⟩, ⟨-, h3⟩, -⟩
    rcases lt_trichotomy (latticePairing A β lam₂) 0 with h2 | h2 | h2
    · left
      refine ⟨⟨⟨hβ, h1⟩, hβI⟩, ⟨hβ, ?_⟩, hβI⟩
      rw [latticePairing_neg_right]
      exact neg_pos.mpr h2
    · exact absurd h2 (h0₂ β hβ)
    · right
      exact ⟨⟨⟨hβ, h2⟩, hβI⟩, ⟨hβ, h3⟩, hβI⟩
  have hdisj : Disjoint ((positiveRelativeRoots (a ≫ l₁ ≫ p₁) lam₁ ∩ I) ∩
        (positiveRelativeRoots (a ≫ l₁ ≫ p₁) (-lam₂) ∩ I))
      ((positiveRelativeRoots (a ≫ l₁ ≫ p₁) lam₂ ∩ I) ∩
        (positiveRelativeRoots (a ≫ l₁ ≫ p₁) (-lam₃) ∩ I)) := by
    refine Set.disjoint_left.mpr fun β h h' => ?_
    have hneg' := h.2.1.2
    have hpos := h'.1.1.2
    rw [latticePairing_neg_right] at hneg'
    linarith
  have hsub := union_subset_of_ncard_add_eq (hfin.subset fun _ h => h.1.1.1)
    (hfin.subset fun _ h => h.1.1.1) hcover hdisj hd
  -- The root `α`: the only indivisible root positive on `λ₁` and negative on `λ₂`.
  obtain ⟨α, hα⟩ := Set.ncard_eq_one.mp hd1
  have hαmem : α ∈ (positiveRelativeRoots (a ≫ l₁ ≫ p₁) lam₁ ∩ I) ∩
      (positiveRelativeRoots (a ≫ l₁ ≫ p₁) (-lam₂) ∩ I) := by
    rw [hα]
    exact Set.mem_singleton α
  have hα1 : 0 < latticePairing A α lam₁ := hαmem.1.1.2
  have hα2 : latticePairing A α lam₂ < 0 := by
    have := hαmem.2.1.2
    rw [latticePairing_neg_right] at this
    linarith
  have hα3 : latticePairing A α lam₃ < 0 := by
    have := (hsub (Or.inl hαmem)).2.1.2
    rw [latticePairing_neg_right] at this
    linarith
  have hray : ∀ β ∈ relativeRoots (a ≫ l₁ ≫ p₁), 0 < latticePairing A β lam₁ →
      latticePairing A β lam₂ < 0 → ∃ n : ℕ, 0 < n ∧ β = n • α := by
    intro β hβ h1 h2
    obtain ⟨α', ⟨hα'I, hα'1⟩, n, -, hn, rfl⟩ :=
      RelativeRoot.exists_indivisiblePositiveRoot_ray (a ≫ l₁ ≫ p₁) lam₁ hβ h1
    rw [latticePairing_nsmul_left, nat_mul_neg_iff hn] at h2
    have hmem : α' ∈ (positiveRelativeRoots (a ≫ l₁ ≫ p₁) lam₁ ∩ I) ∩
        (positiveRelativeRoots (a ≫ l₁ ≫ p₁) (-lam₂) ∩ I) :=
      ⟨⟨⟨hα'I.1, hα'1⟩, hα'I⟩, ⟨hα'I.1, by rw [latticePairing_neg_right]; linarith⟩, hα'I⟩
    rw [hα] at hmem
    exact ⟨n, hn, by rw [Set.mem_singleton_iff.mp hmem]⟩
  -- The cocharacter `mu` of `L`.
  set c₁ := latticePairing A α lam₁ with hc₁
  set c₂ := -latticePairing A α lam₂ with hc₂
  have hc₁pos : 0 < c₁ := hα1
  have hc₂pos : 0 < c₂ := by rw [hc₂]; linarith
  set mu : cocharacterLattice A := c₂ • lam₁ + c₁ • lam₂ with hmu
  have hpairmu : ∀ β : characterLattice A, latticePairing A β mu =
      c₂ * latticePairing A β lam₁ + c₁ * latticePairing A β lam₂ := by
    intro β
    rw [hmu, map_add, map_zsmul, map_zsmul, smul_eq_mul, smul_eq_mul]
  have hαmu : latticePairing A α mu = 0 := by
    rw [hpairmu, hc₂]
    ring
  have hnegpair : ∀ (β : characterLattice A) (ν : cocharacterLattice A),
      latticePairing A (-β) ν = -latticePairing A β ν := by
    intro β ν
    rw [map_neg, LinearMap.neg_apply]
  -- Roots positive on `λ₁` or on `λ₂` are nonnegative on `mu`.
  have hr1 : ∀ β ∈ relativeRoots (a ≫ l₁ ≫ p₁), 0 ≤ latticePairing A β lam₁ →
      0 ≤ latticePairing A β mu := by
    intro β hβ h
    have h1 : 0 < latticePairing A β lam₁ := lt_of_le_of_ne h (Ne.symm (h0₁ β hβ))
    rcases lt_or_gt_of_ne (h0₂ β hβ) with h2 | h2
    · obtain ⟨n, -, rfl⟩ := hray β hβ h1 h2
      rw [latticePairing_nsmul_left, hαmu, mul_zero]
    · rw [hpairmu]
      nlinarith [mul_pos hc₂pos h1, mul_pos hc₁pos h2]
  have hr2 : ∀ β ∈ relativeRoots (a ≫ l₁ ≫ p₁), 0 ≤ latticePairing A β lam₂ →
      0 ≤ latticePairing A β mu := by
    intro β hβ h
    have h2 : 0 < latticePairing A β lam₂ := lt_of_le_of_ne h (Ne.symm (h0₂ β hβ))
    rcases lt_or_gt_of_ne (h0₁ β hβ) with h1 | h1
    · obtain ⟨n, -, hn⟩ := hray (-β) (hneg β hβ) (by rw [hnegpair]; linarith)
        (by rw [hnegpair]; linarith)
      have : latticePairing A (-β) mu = 0 := by
        rw [hn, latticePairing_nsmul_left, hαmu, mul_zero]
      rw [hnegpair] at this
      linarith
    · rw [hpairmu]
      nlinarith [mul_pos hc₂pos h1, mul_pos hc₁pos h2]
  -- On roots orthogonal to `mu`, `λ₂` and `λ₃` have the same sign.
  have hr3 : ∀ β ∈ relativeRoots (a ≫ l₁ ≫ p₁), latticePairing A β mu = 0 →
      (0 < latticePairing A β lam₂ ∧ 0 < latticePairing A β lam₃) ∨
        (latticePairing A β lam₂ < 0 ∧ latticePairing A β lam₃ < 0) := by
    intro β hβ hz0
    rw [hpairmu] at hz0
    rcases lt_or_gt_of_ne (h0₁ β hβ) with h1 | h1
    · have h2 : 0 < latticePairing A β lam₂ := by nlinarith [mul_neg_of_pos_of_neg hc₂pos h1]
      obtain ⟨n, hn, hβn⟩ := hray (-β) (hneg β hβ) (by rw [hnegpair]; linarith)
        (by rw [hnegpair]; linarith)
      have h3 : latticePairing A (-β) lam₃ < 0 := by
        rw [hβn, latticePairing_nsmul_left]
        exact (nat_mul_neg_iff hn _).mpr hα3
      rw [hnegpair] at h3
      exact Or.inl ⟨h2, by linarith⟩
    · have h2 : latticePairing A β lam₂ < 0 := by nlinarith [mul_pos hc₂pos h1]
      obtain ⟨n, hn, rfl⟩ := hray β hβ h1 h2
      refine Or.inr ⟨h2, ?_⟩
      rw [latticePairing_nsmul_left]
      exact (nat_mul_neg_iff hn _).mpr hα3
  -- A large multiple of `mu` dominates `λ₂` and `λ₃` off the roots of `L`.
  obtain ⟨B, hB⟩ := (hfin.image fun β =>
    |latticePairing A β lam₂| + |latticePairing A β lam₃|).bddAbove
  set n : ℕ := B.toNat + 1 with hn
  have hnB : B + 1 ≤ (n : ℤ) := by
    rw [hn]
    push_cast
    linarith [Int.self_le_toNat B]
  have hpairν : ∀ (β : characterLattice A) (ν : cocharacterLattice A),
      latticePairing A β (ν + n • mu) = latticePairing A β ν + n * latticePairing A β mu := by
    intro β ν
    rw [map_add, map_nsmul, nsmul_eq_mul]
  have hsign : ∀ β ∈ relativeRoots (a ≫ l₁ ≫ p₁),
      (0 < latticePairing A β (lam₂ + n • mu) ∧ 0 < latticePairing A β (lam₃ + n • mu)) ∨
        (latticePairing A β (lam₂ + n • mu) < 0 ∧ latticePairing A β (lam₃ + n • mu) < 0) := by
    intro β hβ
    have hb := hB ⟨β, hβ, rfl⟩
    simp only at hb
    have e2 := abs_nonneg (latticePairing A β lam₂)
    have e3 := abs_nonneg (latticePairing A β lam₃)
    have f2 := neg_abs_le (latticePairing A β lam₂)
    have f3 := neg_abs_le (latticePairing A β lam₃)
    have g2 := le_abs_self (latticePairing A β lam₂)
    have g3 := le_abs_self (latticePairing A β lam₃)
    rw [hpairν, hpairν]
    rcases lt_trichotomy (latticePairing A β mu) 0 with hm | hm | hm
    · right
      constructor <;> nlinarith
    · rw [hm, mul_zero, add_zero, add_zero]
      exact hr3 β hβ hm
    · left
      constructor <;> nlinarith
  -- The parabolics and radicals of `λ₂ + n mu` and `λ₃ + n mu` agree.
  have hPeq : Dynamic.parabolic (CommGroupScheme.groupHom (lam₂ + n • mu) ≫ a ≫ l₁ ≫ p₁) =
      Dynamic.parabolic (CommGroupScheme.groupHom (lam₃ + n • mu) ≫ a ≫ l₁ ≫ p₁) := by
    apply le_antisymm
    · refine (RelativeRoot.parabolic_le_iff_nonnegative_rootSupport dynamicConnected hS
        (a ≫ l₁ ≫ p₁) _ _).mpr fun β hβ h => ?_
      rcases hsign β hβ with h' | h'
      · exact h'.2.le
      · exact absurd h (not_le.mpr h'.1)
    · refine (RelativeRoot.parabolic_le_iff_nonnegative_rootSupport dynamicConnected hS
        (a ≫ l₁ ≫ p₁) _ _).mpr fun β hβ h => ?_
      rcases hsign β hβ with h' | h'
      · exact h'.1.le
      · exact absurd h (not_le.mpr h'.2)
  have hUeq : Dynamic.unipotent (CommGroupScheme.groupHom (lam₂ + n • mu) ≫ a ≫ l₁ ≫ p₁) =
      Dynamic.unipotent (CommGroupScheme.groupHom (lam₃ + n • mu) ≫ a ≫ l₁ ≫ p₁) := by
    apply le_antisymm
    · refine (RelativeRoot.unipotent_le_iff_positive_rootSupport_of_smooth hS
        (a ≫ l₁ ≫ p₁) _ _).mpr fun β hβ h => ?_
      rcases hsign β hβ with h' | h'
      · exact h'.2
      · exact absurd h (not_lt.mpr h'.1.le)
    · refine (RelativeRoot.unipotent_le_iff_positive_rootSupport_of_smooth hS
        (a ≫ l₁ ≫ p₁) _ _).mpr fun β hβ h => ?_
      rcases hsign β hβ with h' | h'
      · exact h'.1
      · exact absurd h (not_lt.mpr h'.2.le)
  -- `M ≤ L = Z(mu)`, and `P₁, P₂ ≤ Q = P(mu)`.
  have hcen : IsCentral (CommGroupScheme.groupHom mu ≫ a) := by
    intro V x
    have := ha.1.2 V (x ≫ (CommGroupScheme.groupHom mu).hom.hom)
    simpa only [Grp.comp_hom_hom, Category.assoc] using this
  have hrep : (SubgroupFunctor.range (l₁ ≫ p₁)).IsRepresentedBy (l₁ ≫ p₁) :=
    ⟨(hl₁.isClosedSubgroup.comp hp₁.isClosedSubgroup).mono_overHom, rfl⟩
  have hML : SubgroupFunctor.range (l₁ ≫ p₁) ≤
      Dynamic.centralizer (CommGroupScheme.groupHom mu ≫ a ≫ l₁ ≫ p₁) :=
    (isCentral_comp_iff_le_dynamicCentralizer hrep a rfl mu).mp hcen
  have hQ₁ : SubgroupFunctor.range p₁ ≤
      Dynamic.parabolic (CommGroupScheme.groupHom mu ≫ a ≫ l₁ ≫ p₁) := by
    rw [hP₁]
    exact (RelativeRoot.parabolic_le_iff_nonnegative_rootSupport dynamicConnected hS
      (a ≫ l₁ ≫ p₁) _ _).mpr hr1
  have hQ₂ : SubgroupFunctor.range p₂ ≤
      Dynamic.parabolic (CommGroupScheme.groupHom mu ≫ a ≫ l₁ ≫ p₁) := by
    rw [hP₂]
    exact (RelativeRoot.parabolic_le_iff_nonnegative_rootSupport dynamicConnected hS
      (a ≫ l₁ ≫ p₁) _ _).mpr hr2
  -- `z ∈ closure (P₁(F) P₂(F)) ⊆ Q(F)`, hence `z ∈ L(F)`.
  have hzcl : z ∈ closure ((pointImage p₁ : Set (rationalPoints G)) *
      (pointImage p₂ : Set (rationalPoints G))) :=
    (bruhatLE_mk_one_iff (pointImage p₁) (pointImage p₂) z).mp hz.1
  have hzQ : z ∈ RationalPoint.parabolic (CommGroupScheme.groupHom mu ≫ a ≫ l₁ ≫ p₁) := by
    refine closure_minimal ?_ (isClosed_dynamic_parabolic k G _) hzcl
    rintro _ ⟨x, hx, y, hy, rfl⟩
    exact Subgroup.mul_mem _ (hQ₁ _ hx) (hQ₂ _ hy)
  have hm₀ : IsClosedSubgroup (l₁ ≫ p₁) := hl₁.isClosedSubgroup.comp hp₁.isClosedSubgroup
  have hzL : z ∈ RationalPoint.levi (CommGroupScheme.groupHom mu ≫ a ≫ l₁ ≫ p₁) :=
    mem_levi_of_mem_parabolic_of_conj _ hzQ fun s =>
      hML _ (conj_cocharPoint_mem_of_torus hm₀ ha.isCentralSplitTorus hi hta htb mu s)
  -- On points of `L`, membership in `P₂` and `P₃` (resp. `N₂` and `N₃`) agree.
  have keyP : ∀ (V : Over (Spec (CommRingCat.of k))) (w : V ⟶ G.X),
      w ∈ (Dynamic.centralizer (CommGroupScheme.groupHom mu ≫ a ≫ l₁ ≫ p₁)).carrier V →
      (w ∈ (SubgroupFunctor.range p₂).carrier V ↔ w ∈ (SubgroupFunctor.range p₃).carrier V) := by
    intro V w hw
    rw [hP₂, hP₃, ← mem_parabolic_add_nsmul_iff (a ≫ l₁ ≫ p₁) lam₂ mu n hw,
      ← mem_parabolic_add_nsmul_iff (a ≫ l₁ ≫ p₁) lam₃ mu n hw, hPeq]
  have keyN : ∀ (V : Over (Spec (CommRingCat.of k))) (w : V ⟶ G.X),
      w ∈ (Dynamic.centralizer (CommGroupScheme.groupHom mu ≫ a ≫ l₁ ≫ p₁)).carrier V →
      (w ∈ (SubgroupFunctor.range (r₂ ≫ p₂)).carrier V ↔
        w ∈ (SubgroupFunctor.range (r₃ ≫ p₃)).carrier V) := by
    intro V w hw
    rw [hN₂, hN₃, ← mem_unipotent_add_nsmul_iff (a ≫ l₁ ≫ p₁) lam₂ mu n hw,
      ← mem_unipotent_add_nsmul_iff (a ≫ l₁ ≫ p₁) lam₃ mu n hw, hUeq]
  -- Conjugation by `z ∈ L(F)`.
  have hconjL : ∀ (V : Over (Spec (CommRingCat.of k))) (y : V ⟶ G.X),
      y ∈ (SubgroupFunctor.range (l₁ ≫ p₁)).carrier V →
      (G.constantPoint z V)⁻¹ * y * G.constantPoint z V ∈
        (Dynamic.centralizer (CommGroupScheme.groupHom mu ≫ a ≫ l₁ ≫ p₁)).carrier V := by
    intro V y hy
    have hc : G.constantPoint z V ∈
        (Dynamic.centralizer (CommGroupScheme.groupHom mu ≫ a ≫ l₁ ≫ p₁)).carrier V :=
      (Dynamic.centralizer _).comp_mem _ hzL
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hc) (hML V hy)) hc
  constructor
  · refine SubgroupFunctor.ext fun V => Subgroup.ext fun y => ?_
    simp only [SubgroupFunctor.inf_carrier, Subgroup.mem_inf,
      MaximalTorusParameterExistence.mem_range_comp_innerIso_iff]
    exact and_congr_right fun hy => keyP V _ (hconjL V y hy)
  · refine SubgroupFunctor.ext fun V => Subgroup.ext fun y => ?_
    simp only [SubgroupFunctor.inf_carrier, Subgroup.mem_inf, ← Category.assoc,
      MaximalTorusParameterExistence.mem_range_comp_innerIso_iff]
    exact and_congr_right fun hy => keyN V _ (hconjL V y hy)

set_option maxHeartbeats 1000000 in
/-- `PQCompositionBruhatStatement`, the Bruhat-order input of the regularity part of Renard
VII.3.5 (i). The Bruhat relations follow from `P₂(F) ⊆ P₁(F) P₃(F)` (the chart
`N₂(F) = (N₁ ∩ N₂)(F) (N̄₁ ∩ N₂)(F)` and `N̄₁ ∩ N₂ ≤ N₃` under the root hypothesis) and from
`mem_levi_of_mem_mul_of_torus`; the equalities are `pqCompositionLeviIntersection`. -/
theorem pqCompositionBruhat : PQCompositionBruhatStatement.{u} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ M P₁ N₁ P₂ N₂ P₃ N₃ Pb₁ Nb₁ Pb₂ Nb₂ Pb₃ Nb₃ p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁
    p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂ p₃ l₃ r₃ hp₃ hl₃ hr₃ hmul₃
    pb₁ lb₁ rb₁ hpb₁ hlb₁ hrb₁ hmulb₁ pb₂ lb₂ rb₂ hpb₂ hlb₂ hrb₂ hmulb₂
    pb₃ lb₃ rb₃ hpb₃ hlb₃ hrb₃ hmulb₃ h21 h31 hb1 hb2 hb3 ho1 ho2 ho3 A a ha rootsIn d hd hd1
    z T i hi ta hta tb htb
  have hLz := pqCompositionLeviIntersection k G hG M P₁ N₁ P₂ N₂ P₃ N₃ Pb₁ Nb₁ Pb₂ Nb₂ Pb₃ Nb₃ p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁
    p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂ p₃ l₃ r₃ hp₃ hl₃ hr₃ hmul₃
    pb₁ lb₁ rb₁ hpb₁ hlb₁ hrb₁ hmulb₁ pb₂ lb₂ rb₂ hpb₂ hlb₂ hrb₂ hmulb₂
    pb₃ lb₃ rb₃ hpb₃ hlb₃ hrb₃ hmulb₃ h21 h31 hb1 hb2 hb3 ho1 ho2 ho3 A a ha hd hd1
    z T i hi ta hta tb htb
  have : Smooth G.X.hom := hG.smooth
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hS : IsSplitTorus A.toGrp := ha.1.1.1
  obtain ⟨lam₁, hR₁, -, hN₁, -, hZ₁, -⟩ :=
    exists_oppositePair_cocharacter hG ha hp₁ hl₁ hr₁ hpb₁ hlb₁ hrb₁ rfl hb1 ho1
  obtain ⟨lam₂, hR₂, hRb₂, hN₂, -, hZ₂, h0₂⟩ :=
    exists_oppositePair_cocharacter hG ha hp₂ hl₂ hr₂ hpb₂ hlb₂ hrb₂ h21 hb2 ho2
  obtain ⟨lam₃, -, hRb₃, hN₃, -, -, h0₃⟩ :=
    exists_oppositePair_cocharacter hG ha hp₃ hl₃ hr₃ hpb₃ hlb₃ hrb₃ h31 hb3 ho3
  -- The root-distance hypothesis in terms of the three cocharacters.
  dsimp only [d, rootsIn] at hd
  rw [hR₁, hR₂, hRb₂, hRb₃] at hd
  set I := RelativeRoot.indivisibleRoots (a ≫ l₁ ≫ p₁) with hI
  have hfin : (relativeRoots (a ≫ l₁ ≫ p₁)).Finite := hS.finite_relativeRoots _
  have hcover : (positiveRelativeRoots (a ≫ l₁ ≫ p₁) lam₁ ∩ I) ∩
      (positiveRelativeRoots (a ≫ l₁ ≫ p₁) (-lam₃) ∩ I) ⊆
      ((positiveRelativeRoots (a ≫ l₁ ≫ p₁) lam₁ ∩ I) ∩
        (positiveRelativeRoots (a ≫ l₁ ≫ p₁) (-lam₂) ∩ I)) ∪
      ((positiveRelativeRoots (a ≫ l₁ ≫ p₁) lam₂ ∩ I) ∩
        (positiveRelativeRoots (a ≫ l₁ ≫ p₁) (-lam₃) ∩ I)) := by
    rintro β ⟨⟨⟨hβ, h1⟩, hβI⟩, ⟨-, h3⟩, -⟩
    rcases lt_trichotomy (latticePairing A β lam₂) 0 with h2 | h2 | h2
    · left
      refine ⟨⟨⟨hβ, h1⟩, hβI⟩, ⟨hβ, ?_⟩, hβI⟩
      rw [latticePairing_neg_right]
      exact neg_pos.mpr h2
    · exact absurd h2 (h0₂ β hβ)
    · right
      exact ⟨⟨⟨hβ, h2⟩, hβI⟩, ⟨hβ, h3⟩, hβI⟩
  have hdisj : Disjoint ((positiveRelativeRoots (a ≫ l₁ ≫ p₁) lam₁ ∩ I) ∩
        (positiveRelativeRoots (a ≫ l₁ ≫ p₁) (-lam₂) ∩ I))
      ((positiveRelativeRoots (a ≫ l₁ ≫ p₁) lam₂ ∩ I) ∩
        (positiveRelativeRoots (a ≫ l₁ ≫ p₁) (-lam₃) ∩ I)) := by
    refine Set.disjoint_left.mpr fun β h h' => ?_
    have hneg := h.2.1.2
    have hpos := h'.1.1.2
    rw [latticePairing_neg_right] at hneg
    linarith
  have hsub := union_subset_of_ncard_add_eq (hfin.subset fun _ h => h.1.1.1)
    (hfin.subset fun _ h => h.1.1.1) hcover hdisj hd
  -- `N̄₁ ∩ N₂ ≤ N₃`: a root positive on `λ₂` and on `-λ₁` is positive on `λ₃`.
  have hKA := RelativeRoot.dynamicUnipotent_inf_le_of_positiveRoots hG.smooth hG.connectedSpace
    hS (a ≫ l₁ ≫ p₁) (-lam₁) lam₂ lam₃ (by
      intro β hβ h1
      by_contra hneg
      have h3 : latticePairing A β lam₃ < 0 := lt_of_le_of_ne (not_lt.mp hneg) (h0₃ β hβ.1)
      obtain ⟨α, ⟨hαI, hα2⟩, n, -, hn, rfl⟩ :=
        RelativeRoot.exists_indivisiblePositiveRoot_ray (a ≫ l₁ ≫ p₁) lam₂ hβ.1 hβ.2
      rw [latticePairing_nsmul_left, nat_mul_neg_iff hn] at h3
      rw [latticePairing_neg_right, latticePairing_nsmul_left, neg_pos, nat_mul_neg_iff hn] at h1
      have hαX := hsub (Or.inr ⟨⟨⟨hαI.1, hα2⟩, hαI⟩,
        ⟨hαI.1, by rw [latticePairing_neg_right]; linarith⟩, hαI⟩)
      have := hαX.1.1.2
      linarith)
  rw [groupHom_neg_comp_eq_oppositeCocharacter] at hKA
  -- `P₂(F) ⊆ P₁(F) P₃(F)`.
  have hd₂ : IsSemidirectDecomposition (pointImage p₂) (pointImage (l₁ ≫ p₁))
      (pointImage (r₂ ≫ p₂)) := by
    rw [← h21]
    exact isSemidirectDecomposition_pointImage p₂ l₂ r₂ hp₂.isClosedSubgroup hr₂ hmul₂
  have hsubset : (pointImage p₂ : Set (rationalPoints G)) ⊆
      (pointImage p₁ : Set (rationalPoints G)) * (pointImage p₃ : Set (rationalPoints G)) := by
    intro x hx
    obtain ⟨m, hm, n, hn, rfl⟩ := hd₂.exists_mul_eq hx
    have hZ : (Dynamic.centralizer (CommGroupScheme.groupHom lam₂ ≫ a ≫ l₁ ≫ p₁)).carrier
          (Over.mk (𝟙 _)) =
        (Dynamic.centralizer (CommGroupScheme.groupHom lam₁ ≫ a ≫ l₁ ≫ p₁)).carrier
          (Over.mk (𝟙 _)) := by
      rw [← hZ₂, ← hZ₁]
    rw [hN₂] at hn
    obtain ⟨b, hb, c, hc, rfl⟩ := exists_mul_eq_of_secondChart hZ hn
    have hb' : b ∈ pointImage (r₁ ≫ p₁) := by
      rw [hN₁]
      exact hb
    have hc' : c ∈ pointImage (r₃ ≫ p₃) := by
      rw [hN₃]
      exact hKA hc
    refine ⟨m * b, Subgroup.mul_mem _ (pointImage_comp_le p₁ l₁ hm)
      (pointImage_comp_le p₁ r₁ hb'), c, pointImage_comp_le p₃ r₃ hc', ?_⟩
    beta_reduce
    rw [mul_assoc]
  have hM₁ : pointImage (l₁ ≫ p₁) ≤ pointImage p₁ := pointImage_comp_le p₁ l₁
  have hM₂ : pointImage (l₁ ≫ p₁) ≤ pointImage p₂ := by
    rw [← h21]
    exact pointImage_comp_le p₂ l₂
  obtain ⟨h1, h2⟩ := bruhatLT_mk_one_of_subset_mul hsubset hM₁ hM₂ fun hz =>
    mem_levi_of_mem_mul_of_torus hG hp₁ hl₁ hr₁ hmul₁ hp₃ hl₃ hr₃ hmul₃ hpb₁ hlb₁ hrb₁
      hpb₃ hlb₃ hrb₃ hmulb₃ h31 hb1 hb3 ho1 ho3 ha hi hta htb hz
  exact ⟨h1, fun h => ⟨h2 h, hLz h⟩⟩

/-- Premise (4) of the published reduction of Renard VII.3.5 (i): every `P₁P₃`-regular `σ` is
`P₂P₃`- and `P₁P₂`-regular. It is the published reduction `pqCompositionRegularityOfBruhat`
applied to `pqCompositionBruhat`. -/
theorem pqCompositionRegularity : PQCompositionRegularityStatement.{u, v} :=
  pqCompositionRegularityOfBruhat pqCompositionBruhat

end Langlands.Aubert.General.RepresentedParabolic
