import Langlands.Representation.Jacquet.StandardCasselmanPairing
import Langlands.Representation.Aubert.General.RationalCartanLatticeModel
import Langlands.GroupScheme.Rational.MaximalLeviConeComplementLine
import Langlands.GroupScheme.Rational.StandardLeviLieWeights
import Langlands.GroupScheme.Rational.StandardParabolicOrderFromRoots
import Langlands.GroupScheme.Rational.RelativeRootSignInclusionsProof
import Langlands.GroupScheme.Dynamic.LieProof

/-! # Uniform Casselman asymptotics for actual standard parabolics (Waldspurger, Proposition I.4.3)

For a connected reductive group over a nonarchimedean local field, with Renard's simultaneous
basis data (V.5.2) for all standard parabolic subgroups `P_J = M_J U_J` and standard
cocharacters, this module proves the inclusions `U_J ⊆ U_∅`, `Ū_J ⊆ Ū_∅` and Waldspurger's
Proposition I.4.3
(Casselman) on the dominant points `Ā_0^+` of the maximal split torus: for an admissible
representation there are Casselman pairings `b_J` for all `J ⊆ Δ` (those of Théorème I.4.1) and,
for each vector and smooth functional, one threshold that makes the asymptotic identity hold for
every dominant point and every `J` outside of which the point is deep. The identity is stated
without the modulus factor; see the paired Markdown for the dictionary.
-/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.BruhatTits.SpecialCompact

section Lattice

variable {F : Type u} [Field F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S} {J : Set (characterLattice S)}
  {A : CommGroupScheme (Spec (CommRingCat.of F))} {q : A.toGrp ⟶ S.toGrp}

/-- Cocharacters of a compatible split component of `M_J`, pushed into the maximal split torus,
are orthogonal to the simple roots in `J`. -/
theorem IsCompatibleStandardSplitComponent.latticePairing_eq_zero
    [LocallyOfFiniteType G.X.hom]
    (hA : IsCompatibleStandardSplitComponent i ν J A q)
    (hJ : J ⊆ simpleRelativeRoots i ν) (c : cocharacterLattice A)
    {α : characterLattice S} (hα : α ∈ J) :
    latticePairing S α (RealTorusSpace.cocharacterMapInt (Additive.ofMul q : A ⟶ S) c) = 0 := by
  obtain ⟨_, M, j, a, hj, _, hM, ha, hcompat⟩ := hA
  have : IsAffineHom M.X.hom := hM.isAffineHom
  have : Smooth M.X.hom := hM.smooth
  have : Mono j.hom.hom := hj.1
  let t := standardLeviTorusFactor i ν J hj
  have hf : CommGroupScheme.groupHom (Additive.ofMul q : A ⟶ S) ≫ t = a := by
    apply Grp.hom_ext
    apply (cancel_mono j.hom.hom).mp
    rw [← Grp.comp_hom_hom, ← Grp.comp_hom_hom, Category.assoc,
      standardLeviTorusFactor_comp, hcompat]
    rfl
  have hroot : α ∈ relativeRoots t :=
    selectedRoots_subset_relativeRoots_standardLeviTorusFactor dynamicLie i ν J hj hJ hα
  have hc : IsCentral (CommGroupScheme.groupHom c ≫ a) :=
    ha.isCentralSplitTorus.isCentral.comp _
  have h := MaximalLeviConeComplementLine.latticePairing_restrict_eq_zero_of_isCentral t
    (Additive.ofMul q : A ⟶ S) hf hroot hc
  rwa [RelativeRoot.latticePairing_restrict_cocharacterMapInt] at h

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- A point of the weak chamber of a compatible split component of `M_J` is the uniformizer power
`ϖ^y = i(y(ϖ))` of a cocharacter `y` orthogonal to `J` and nonnegative on every simple root. -/
theorem IsCompatibleStandardSplitComponent.exists_eq_uniformizerPowers
    [LocallyOfFiniteType G.X.hom]
    (hA : IsCompatibleStandardSplitComponent i ν J A q)
    (hJ : J ⊆ simpleRelativeRoots i ν) {g : rationalPoints G}
    (hg : g ∈ standardComponentCAplus i ν J q) :
    ∃ y : cocharacterLattice S, g = Aubert.General.uniformizerPowers i (.ofAdd y) ∧
      (∀ α ∈ J, latticePairing S α y = 0) ∧
      ∀ α ∈ simpleRelativeRoots i ν, 0 ≤ latticePairing S α y := by
  obtain ⟨x, ⟨⟨c, rfl⟩, hx⟩, rfl⟩ := hg
  obtain ⟨c, rfl⟩ := Multiplicative.ofAdd.surjective c
  refine ⟨RealTorusSpace.cocharacterMapInt (Additive.ofMul q : A ⟶ S) c, ?_, ?_, ?_⟩
  · change rationalPoints.map i (rationalPoints.map
      (CommGroupScheme.groupHom (Additive.ofMul q : A ⟶ S))
        (Plancherel.RenardCartan.uniformizerSection A (.ofAdd c))) = _
    rw [Plancherel.RenardCartan.uniformizerSection_naturality]
    rfl
  · intro α hα
    exact hA.latticePairing_eq_zero hJ c hα
  · intro α hα
    by_cases hαJ : α ∈ J
    · exact (hA.latticePairing_eq_zero hJ c hαJ).ge
    · have h := hx _ ⟨α, ⟨hα, hαJ⟩, rfl⟩
      rw [CocharacterUniformizer.characterNorm_latticeSection,
        Aubert.General.latticePairing_componentCharacterRestriction] at h
      have hq : (1 : ℝ) < LocalField.residueCardinality F := by
        exact_mod_cast LocalField.residueCardinality_gt_one F
      by_contra hneg
      have h1 : (1 : ℝ) < (LocalField.residueCardinality F : ℝ) ^
          (-(latticePairing S α (c ≫ Additive.ofMul q))) :=
        one_lt_zpow₀ hq (by
          have : latticePairing S α (c ≫ Additive.ofMul q) < 0 := not_le.mp hneg
          omega)
      linarith

/-- A uniformizer power `ϖ^y` with `y` orthogonal to `J` and nonnegative on every simple root
lies in the lattice `C_A` and the weak chamber `C_A^+` of every compatible split component of
`M_J`. -/
theorem uniformizerPowers_mem_standardComponentChambers [LocallyOfFiniteType G.X.hom]
    (hi : IsMaximalSplitTorus i)
    (hexists : ∃ ζ, IsStandardCocharacter i ν J ζ)
    (hA : IsCompatibleStandardSplitComponent i ν J A q)
    (y : cocharacterLattice S) (hy : ∀ β ∈ J, latticePairing S β y = 0)
    (hnonneg : ∀ β ∈ simpleRelativeRoots i ν, 0 ≤ latticePairing S β y) :
    Aubert.General.uniformizerPowers i (.ofAdd y) ∈ standardComponentCA i q ∧
      Aubert.General.uniformizerPowers i (.ofAdd y) ∈ standardComponentCAplus i ν J q := by
  have hfinite := hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν
  obtain ⟨c, rfl⟩ : ∃ c : cocharacterLattice A,
      RealTorusSpace.cocharacterMapInt (Additive.ofMul q : A ⟶ S) c = y := by
    obtain ⟨_, M, jM, a, hjM, hjMc, hMred, ha, haq⟩ := hA
    have : IsAffineHom M.X.hom := hMred.isAffineHom
    let t := standardLeviTorusFactor i ν J hjM
    have : Mono t.hom.hom.left :=
      (hi.isMaximalSplitTorus_standardLeviTorusFactor i ν _ hjM hjMc).isSplitSubtorus.mono
    have hf : CommGroupScheme.groupHom (Additive.ofMul q : A ⟶ S) ≫ t = a := by
      have : Mono jM.hom.hom := hjM.1
      apply Grp.hom_ext
      apply (cancel_mono jM.hom.hom).mp
      rw [← Grp.comp_hom_hom, ← Grp.comp_hom_hom, Category.assoc,
        standardLeviTorusFactor_comp, haq]
      rfl
    have hyc : y ∈ centralCocharacters t :=
      isCentral_standardLeviTorusFactor_of_annihilates i ν J hjM hfinite hexists y hy
    rw [← ha.range_cocharacterMapInt_eq_centralCocharacters _ hf] at hyc
    exact hyc
  let p := CocharacterUniformizer.latticeSection F A (.ofAdd c)
  have hp : p ∈ CocharacterUniformizer.CA F A := ⟨.ofAdd c, rfl⟩
  have heq : rationalPoints.map (q ≫ i) p = Aubert.General.uniformizerPowers i
      (.ofAdd (RealTorusSpace.cocharacterMapInt (Additive.ofMul q : A ⟶ S) c)) := by
    change rationalPoints.map i (rationalPoints.map
      (CommGroupScheme.groupHom (Additive.ofMul q : A ⟶ S))
        (Plancherel.RenardCartan.uniformizerSection A (.ofAdd c))) = _
    rw [Plancherel.RenardCartan.uniformizerSection_naturality]
    rfl
  have hq : (1 : ℝ) < LocalField.residueCardinality F := by
    exact_mod_cast LocalField.residueCardinality_gt_one F
  refine ⟨⟨p, hp, heq⟩, ⟨p, ⟨hp, ?_⟩, heq⟩⟩
  rintro _ ⟨β, ⟨hβ, -⟩, rfl⟩
  rw [CocharacterUniformizer.characterNorm_latticeSection,
    Aubert.General.latticePairing_componentCharacterRestriction]
  exact zpow_le_one_of_nonpos₀ hq.le (neg_nonpos.mpr (hnonneg β hβ))

end Lattice

section Order

variable {F : Type u} [Field F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

/-- `U_J ⊆ U_∅` on rational points, for every face `J` with a standard cocharacter `ζ`: every
relative root positive on `ζ` is positive on every standard cocharacter of the empty face, so the
proved root-sign comparison of dynamic unipotent subgroups applies. -/
theorem standardUnipotentPoints_le_empty (hG : IsConnectedReductive G) {i : S.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i) {ν : cocharacterLattice S} (hν : IsGenericCocharacter i ν)
    {J : Set (characterLattice S)} {ζ : cocharacterLattice S}
    (hζ : IsStandardCocharacter i ν J ζ) :
    standardUnipotentPoints i ν J ≤ standardUnipotentPoints i ν ∅ := by
  have hneg := relativeRootNegation F G hG S i hi
  intro g hg
  rw [mem_standardUnipotent]
  intro ζ' hζ'
  have hle := (relativeRootSignInclusions F G hG S i hi ζ ζ').2 fun α hα hpos =>
    (hζ'.root_pairing_implications_of_subset i ν hν hneg hζ (Set.empty_subset J) hα).2.2 hpos
  exact hle _ (standardUnipotent_le_dynamicUnipotent i ν hζ _ hg)

/-- `Ū_J ⊆ Ū_∅` on rational points, for every face `J` with a standard cocharacter: the previous
inclusion for the reversed chamber `-ν`, the face `-J` and the cocharacter `-ζ`. -/
theorem standardOppositeUnipotentPoints_le_empty (hG : IsConnectedReductive G)
    {i : S.toGrp ⟶ G} (hi : IsMaximalSplitTorus i) {ν : cocharacterLattice S}
    (hν : IsGenericCocharacter i ν) {J : Set (characterLattice S)} {ζ : cocharacterLattice S}
    (hζ : IsStandardCocharacter i ν J ζ) :
    standardOppositeUnipotentPoints i ν J ≤ standardOppositeUnipotentPoints i ν ∅ := by
  have hneg := relativeRootNegation F G hG S i hi
  have h := standardUnipotentPoints_le_empty hG hi (hν.neg i ν) (hζ.neg i ν hneg)
  simpa only [standardOppositeUnipotentPoints, Set.image_empty] using h

end Order

section Face

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

/-- **Waldspurger's face `Δ_0^{M_{m,t}}`** (Proposition I.4.3) for a point `x` of the maximal split
torus `S(F)` and `t ∈ ℝ`: the simple roots `α` with `⟨α, H_0(x)⟩ ≤ t`, that is
`|α(x)|_F ≥ q^{-t}` for the residue cardinality `q`. The standard parabolic subgroup with this
face is the source's `P_{m,t}` for `m = x`. -/
def waldspurgerFace (i : S.toGrp ⟶ G) (ν : cocharacterLattice S) (t : ℝ)
    (x : rationalPoints S.toGrp) : Set (characterLattice S) :=
  {α | α ∈ simpleRelativeRoots i ν ∧
    (LocalField.residueCardinality F : ℝ) ^ (-t) ≤ CocharacterUniformizer.characterNorm F S α x}

theorem waldspurgerFace_subset (i : S.toGrp ⟶ G) (ν : cocharacterLattice S) (t : ℝ)
    (x : rationalPoints S.toGrp) : waldspurgerFace i ν t x ⊆ simpleRelativeRoots i ν :=
  fun _ h => h.1

end Face

section Uniform

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] standardCasselmanIsAffine standardCasselmanTopology
  standardCasselmanTopologicalGroup

variable (hG : IsConnectedReductive G) {i : S.toGrp ⟶ G} (hi : IsMaximalSplitTorus i)
  {ν : cocharacterLattice S} (hν : IsGenericCocharacter i ν)
  {K0 : Subgroup (rationalPoints G)} {B : Set (Subgroup (rationalPoints G))}
  (hB : CompactOpenNormalBasis K0 B)
  (A : Set (characterLattice S) → CommGroupScheme (Spec (CommRingCat.of F)))
  (q : ∀ J, (A J).toGrp ⟶ S.toGrp)
  (hA : ∀ J, J ⊆ simpleRelativeRoots i ν →
    IsCompatibleStandardSplitComponent i ν J (A J) (q J))
  (hmem : ∀ J, J ⊆ simpleRelativeRoots i ν → ∀ K ∈ B,
    StandardParabolicBasisMember i ν J (q J) K)
  (ζ : Set (characterLattice S) → cocharacterLattice S)
  (hζ : ∀ J, J ⊆ simpleRelativeRoots i ν → IsStandardCocharacter i ν J (ζ J))

include hi hA hζ in
/-- Dominant uniformizer powers lie in the lattice and the weak chamber of the split component
of the minimal standard Levi `M_∅`. -/
theorem uniformizerPowers_mem_emptyChambers (y : cocharacterLattice S)
    (hy : ∀ β ∈ simpleRelativeRoots i ν, 0 ≤ latticePairing S β y) :
    Aubert.General.uniformizerPowers i (.ofAdd y) ∈ standardComponentCA i (q ∅) ∧
      Aubert.General.uniformizerPowers i (.ofAdd y) ∈
        standardComponentCAplus i ν ∅ (q ∅) :=
  uniformizerPowers_mem_standardComponentChambers hi ⟨ζ ∅, hζ ∅ (Set.empty_subset _)⟩
    (hA ∅ (Set.empty_subset _)) y (fun _ h => by simp at h) hy

include hG hi hν hA hmem hζ in
/-- **Depth control.** For a finite subset `Fs` of `U_J` and a basis member `K`, there is a
threshold `T` such that conjugation by every dominant uniformizer power `ϖ^y` with
`⟨α, y⟩ > T` for all simple roots `α ∉ J` maps `Fs` into `K`. Write `y = yr + m₀ z`, where
`ϖ^z` is the chosen strict element of `M_J`: its powers pull `Fs` into `K ∩ U_J`, and the dominant
remainder `ϖ^yr` keeps `K ∩ U_∅ ⊇ K ∩ U_J` inside `K`. -/
theorem exists_conj_mem_of_deep {J : Set (characterLattice S)}
    (hJ : J ⊆ simpleRelativeRoots i ν) {K : Subgroup (rationalPoints G)} (hK : K ∈ B)
    (Fs : Finset (rationalPoints G))
    (hFs : (Fs : Set (rationalPoints G)) ⊆ standardUnipotentPoints i ν J) :
    ∃ T : ℝ, ∀ y : cocharacterLattice S,
      (∀ α ∈ simpleRelativeRoots i ν, 0 ≤ latticePairing S α y) →
      (∀ α ∈ simpleRelativeRoots i ν, α ∉ J → T < latticePairing S α y) →
      ∀ n ∈ Fs, Aubert.General.uniformizerPowers i (.ofAdd y) * n *
        (Aubert.General.uniformizerPowers i (.ofAdd y))⁻¹ ∈ K := by
  classical
  have hfinite := hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν
  set g := (hA J hJ).strictElement i ν hi (hζ J hJ) with hg_def
  obtain ⟨-, -, hgplus, hgstrict⟩ := (hA J hJ).strictElement_spec i ν hi (hζ J hJ)
  obtain ⟨z, hgz, hz0, -⟩ := (hA J hJ).exists_eq_uniformizerPowers hJ hgplus
  obtain ⟨-, hcon⟩ := hmem J hJ K hK
  have hcontr : ∀ r : ℕ, ∀ x ∈ K ⊓ standardUnipotentPoints i ν J,
      g ^ r * x * (g ^ r)⁻¹ ∈ K ⊓ standardUnipotentPoints i ν J := by
    intro r
    induction r with
    | zero => intro x hx; simpa using hx
    | succ r ih =>
      intro x hx
      have h2 : g * (g ^ r * x * (g ^ r)⁻¹) * g⁻¹ ∈ K ⊓ standardUnipotentPoints i ν J :=
        (hcon.2.1 g hgplus).1 ⟨_, ih x hx, rfl⟩
      have h3 : g ^ (r + 1) * x * (g ^ (r + 1))⁻¹ = g * (g ^ r * x * (g ^ r)⁻¹) * g⁻¹ := by
        group
      rw [h3]
      exact h2
  have hpull : ∀ n ∈ Fs, ∃ r : ℕ, ∀ s : ℕ, r ≤ s →
      g ^ s * n * (g ^ s)⁻¹ ∈ K ⊓ standardUnipotentPoints i ν J := by
    intro n hn
    have hnU : n ∈ (standardUnipotentPoints i ν J : Set (rationalPoints G)) := hFs hn
    rw [(hcon.2.2.1 g hgstrict).1] at hnU
    obtain ⟨r, x, hx, hxn⟩ := Set.mem_iUnion.mp hnU
    refine ⟨r, fun s hrs => ?_⟩
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hrs
    have hx' : g ^ r * n * (g ^ r)⁻¹ = x := by
      rw [← hxn]
      group
    have h3 : g ^ (r + d) * n * (g ^ (r + d))⁻¹ =
        g ^ d * (g ^ r * n * (g ^ r)⁻¹) * (g ^ d)⁻¹ := by
      group
    rw [h3, hx']
    exact hcontr d x hx
  choose! r hr using hpull
  set m₀ := Fs.sup r with hm₀
  set C : ℤ := ∑ α ∈ hfinite.toFinset, |latticePairing S α z| with hC
  refine ⟨(m₀ : ℝ) * C, fun y hy hdeep n hn => ?_⟩
  set yr := y - m₀ • z with hyr_def
  have hyr : ∀ α ∈ simpleRelativeRoots i ν, 0 ≤ latticePairing S α yr := by
    intro α hα
    have hlin : latticePairing S α yr = latticePairing S α y - m₀ * latticePairing S α z := by
      rw [hyr_def, map_sub, map_nsmul, nsmul_eq_mul]
    by_cases hαJ : α ∈ J
    · rw [hlin, hz0 α hαJ, mul_zero, sub_zero]
      exact hy α hα
    · have hle : latticePairing S α z ≤ C :=
        (le_abs_self _).trans (Finset.single_le_sum (f := fun α => |latticePairing S α z|)
          (fun _ _ => abs_nonneg _) (hfinite.mem_toFinset.mpr hα))
      have hd : (m₀ : ℤ) * C < latticePairing S α y := by
        have := hdeep α hα hαJ
        exact_mod_cast this
      have hm : (m₀ : ℤ) * latticePairing S α z ≤ m₀ * C :=
        mul_le_mul_of_nonneg_left hle (by positivity)
      rw [hlin]
      linarith
  obtain ⟨-, hbplus⟩ := uniformizerPowers_mem_emptyChambers hi A q hA ζ hζ yr hyr
  obtain ⟨-, hcon₀⟩ := hmem ∅ (Set.empty_subset _) K hK
  have hsplit : Aubert.General.uniformizerPowers i (.ofAdd y) =
      Aubert.General.uniformizerPowers i (.ofAdd yr) * g ^ m₀ := by
    have hgz' : g = Aubert.General.uniformizerPowers i (.ofAdd z) := hgz
    rw [hgz', ← map_pow, ← map_mul, ← ofAdd_nsmul, ← ofAdd_add, hyr_def, sub_add_cancel]
  have hgn := hr n hn m₀ (Finset.le_sup hn)
  have hU' : g ^ m₀ * n * (g ^ m₀)⁻¹ ∈ K ⊓ standardUnipotentPoints i ν ∅ :=
    ⟨hgn.1, standardUnipotentPoints_le_empty hG hi hν (hζ J hJ) hgn.2⟩
  have hfin := (hcon₀.2.1 _ hbplus).1 ⟨_, hU', rfl⟩
  rw [hsplit]
  have h4 : Aubert.General.uniformizerPowers i (.ofAdd yr) * g ^ m₀ * n *
      (Aubert.General.uniformizerPowers i (.ofAdd yr) * g ^ m₀)⁻¹ =
      Aubert.General.uniformizerPowers i (.ofAdd yr) * (g ^ m₀ * n * (g ^ m₀)⁻¹) *
        (Aubert.General.uniformizerPowers i (.ofAdd yr))⁻¹ := by
    group
  rw [h4]
  exact hfin.1

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

include hG hi hν hB hA hmem hζ in
open Langlands.Jacquet in
/-- **Waldspurger, Proposition I.4.3, on the dominant uniformizer lattice.** For an admissible
smooth representation `ρ` of `G(F)` there are bilinear forms `b J` on `V̌_{Ū_J} × V_{U_J}`, one for
every `J ⊆ Δ`, nondegenerate on both sides and invariant under `M_J` (the Casselman pairings of
Théorème I.4.1), such that for every `v ∈ V` and smooth functional `ℓ` one threshold `T` works for
all faces at once: `ℓ(ρ(ϖ^λ) v) = b J (ǰ(ℓ), j(ρ(ϖ^λ) v))` for every dominant cocharacter `λ` and
every `J ⊆ Δ` with `⟨α, λ⟩ > T` for all simple roots `α ∉ J`. -/
theorem exists_uniform_standardCasselmanPairing (ρ : Representation ℂ (rationalPoints G) V)
    (hρ : IsAdmissible ρ) :
    ∃ b : ∀ J : Set (characterLattice S),
        Coinvariants (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J) →ₗ[ℂ]
          Coinvariants ρ (standardUnipotentPoints i ν J) →ₗ[ℂ] ℂ,
      (∀ J, J ⊆ simpleRelativeRoots i ν →
        Function.Injective (b J) ∧ Function.Injective (b J).flip ∧
        ∀ (hMN : standardLeviPoints i ν J ≤
            Subgroup.normalizer (standardOppositeUnipotentPoints i ν J))
          (m : standardLeviPoints i ν J)
          (x : Coinvariants (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J))
          (y : Coinvariants ρ (standardUnipotentPoints i ν J)),
          b J (action (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J)
              (standardLeviPoints i ν J) hMN m x)
            (action ρ (standardUnipotentPoints i ν J) (standardLeviPoints i ν J)
              (standardLeviPoints_le_normalizer_standardUnipotentPoints i ν J) m y) =
            b J x y) ∧
      ∀ (v : V) (ℓ : SmoothDual ρ), ∃ T : ℝ, ∀ lam : cocharacterLattice S,
        (∀ α ∈ simpleRelativeRoots i ν, 0 ≤ latticePairing S α lam) →
        ∀ J, J ⊆ simpleRelativeRoots i ν →
        (∀ α ∈ simpleRelativeRoots i ν, α ∉ J → T < latticePairing S α lam) →
          smoothDualPairing ρ ℓ (ρ (Aubert.General.uniformizerPowers i (.ofAdd lam)) v) =
            b J (Jacquet.mk (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J) ℓ)
              (Jacquet.mk ρ (standardUnipotentPoints i ν J)
                (ρ (Aubert.General.uniformizerPowers i (.ofAdd lam)) v)) := by
  classical
  have hfinite := hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν
  have hbex : ∀ J : Set (characterLattice S), ∃ bJ :
      Coinvariants (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J) →ₗ[ℂ]
        Coinvariants ρ (standardUnipotentPoints i ν J) →ₗ[ℂ] ℂ,
      ∀ hJ : J ⊆ simpleRelativeRoots i ν,
        (standardCasselmanPairingData hG hi hν (hζ J hJ) hB (hA J hJ)
          (hmem J hJ)).IsStablePairing ρ hρ.1 bJ ∧
        Function.Injective bJ ∧ Function.Injective bJ.flip ∧
        ∀ (hMN : standardLeviPoints i ν J ≤
            Subgroup.normalizer (standardOppositeUnipotentPoints i ν J))
          (m : standardLeviPoints i ν J)
          (x : Coinvariants (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J))
          (y : Coinvariants ρ (standardUnipotentPoints i ν J)),
          bJ (action (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J)
              (standardLeviPoints i ν J) hMN m x)
            (action ρ (standardUnipotentPoints i ν J) (standardLeviPoints i ν J)
              (standardLeviPoints_le_normalizer_standardUnipotentPoints i ν J) m y) =
            bJ x y := by
    intro J
    by_cases hJ : J ⊆ simpleRelativeRoots i ν
    · let D := standardCasselmanPairingData hG hi hν (hζ J hJ) hB (hA J hJ) (hmem J hJ)
      have hAd : D.Admits ρ hρ.1 :=
        standardCasselmanPairingData_admits hG hi hν (hζ J hJ) hB (hA J hJ) (hmem J hJ) ρ hρ
      obtain ⟨bJ, hbJ⟩ := D.exists_isStablePairing hAd
      exact ⟨bJ, fun _ => ⟨hbJ, hbJ.injective hAd, hbJ.flip_injective hAd,
        fun _ => hbJ.map_action hAd⟩⟩
    · exact ⟨0, fun h => absurd h hJ⟩
  choose b hb using hbex
  refine ⟨b, fun J hJ => (hb J hJ).2, ?_⟩
  intro v ℓ
  obtain ⟨U₁, hU₁⟩ := hρ.1 v
  obtain ⟨U₂, hU₂⟩ := isSmooth_smoothContragredient ρ ℓ
  obtain ⟨K, hKB, hKU⟩ := hB.2.mem_iff.mp (U₁ ⊓ U₂).mem_nhds_one
  have hle₁ : basisOpenSubgroup hB hKB ≤ U₁ := fun x hx => (hKU hx).1
  have hle₂ : basisOpenSubgroup hB hKB ≤ U₂ := fun x hx => (hKU hx).2
  have hv := mem_fixedVectors_of_le ρ hle₁ hU₁
  have hℓ := mem_fixedVectors_of_le (smoothContragredient ρ) hle₂ hU₂
  have hTex : ∀ J : Set (characterLattice S), ∃ T : ℝ, ∀ hJ : J ⊆ simpleRelativeRoots i ν,
      ∀ lam : cocharacterLattice S,
        (∀ α ∈ simpleRelativeRoots i ν, 0 ≤ latticePairing S α lam) →
        (∀ α ∈ simpleRelativeRoots i ν, α ∉ J → T < latticePairing S α lam) →
          smoothDualPairing ρ ℓ (ρ (Aubert.General.uniformizerPowers i (.ofAdd lam)) v) =
            b J (Jacquet.mk (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J) ℓ)
              (Jacquet.mk ρ (standardUnipotentPoints i ν J)
                (ρ (Aubert.General.uniformizerPowers i (.ofAdd lam)) v)) := by
    intro J
    by_cases hJ : J ⊆ simpleRelativeRoots i ν
    swap
    · exact ⟨0, fun h => absurd h hJ⟩
    let D := standardCasselmanPairingData hG hi hν (hζ J hJ) hB (hA J hJ) (hmem J hJ)
    have hAd : D.Admits ρ hρ.1 :=
      standardCasselmanPairingData_admits hG hi hν (hζ J hJ) hB (hA J hJ) (hmem J hJ) ρ hρ
    have hKgood : D.Good (basisOpenSubgroup hB hKB) :=
      good_of_mem hG hi hν (hζ J hJ) hB (hA J hJ) (hmem J hJ) hKB
    obtain ⟨Fs, hFs, hasym⟩ := (hb J hJ).1.exists_finset_asymptotics_of_commute hAd
      (basisOpenSubgroup hB hKB) hKgood hv hℓ
    obtain ⟨T, hT⟩ := exists_conj_mem_of_deep hG hi hν A q hA hmem ζ hζ hJ hKB Fs hFs
    refine ⟨T, fun _ lam hlam hdeep => ?_⟩
    set K' := basisOpenSubgroup hB hKB with hK'
    set a := Aubert.General.uniformizerPowers i (.ofAdd lam) with ha_def
    set g := (hA J hJ).strictElement i ν hi (hζ J hJ) with hg_def
    obtain ⟨-, -, hgplus, -⟩ := (hA J hJ).strictElement_spec i ν hi (hζ J hJ)
    obtain ⟨z, hgz, -, hznn⟩ := (hA J hJ).exists_eq_uniformizerPowers hJ hgplus
    have hgz' : g = Aubert.General.uniformizerPowers i (.ofAdd z) := hgz
    obtain ⟨haCA, haplus⟩ := uniformizerPowers_mem_emptyChambers hi A q hA ζ hζ lam hlam
    obtain ⟨hgCA₀, hgplus₀⟩ : g ∈ standardComponentCA i (q ∅) ∧
        g ∈ standardComponentCAplus i ν ∅ (q ∅) := by
      rw [hgz']
      exact uniformizerPowers_mem_emptyChambers hi A q hA ζ hζ z hznn
    obtain ⟨hfac₀, hcon₀⟩ := hmem ∅ (Set.empty_subset _) K hKB
    have hfactor : ∀ k ∈ K',
        ∃ l ∈ K'.toSubgroup ⊓ standardOppositeUnipotentPoints i ν ∅,
        ∃ m ∈ K'.toSubgroup ⊓ standardLeviPoints i ν ∅,
        ∃ u ∈ K'.toSubgroup ⊓ standardUnipotentPoints i ν ∅, k = l * m * u := by
      intro k hk
      obtain ⟨⟨l, m, n⟩, heq⟩ := hfac₀.2 ⟨k, hk⟩
      exact ⟨l, l.property, m, m.property, n, n.property, (congrArg Subtype.val heq).symm⟩
    have hup : ∀ c ∈ standardComponentCAplus i ν ∅ (q ∅),
        ∀ u ∈ K'.toSubgroup ⊓ standardUnipotentPoints i ν ∅, c * u * c⁻¹ ∈ K' :=
      fun c hc u hu => ((hcon₀.2.1 c hc).1 ⟨u, hu, rfl⟩).1
    have hlow : ∀ c ∈ standardComponentCAplus i ν ∅ (q ∅),
        ∀ l ∈ K'.toSubgroup ⊓ standardOppositeUnipotentPoints i ν ∅,
          c⁻¹ * l * c ∈ K' := fun c hc l hl => by
      have h := (hcon₀.2.1 c hc).2 ⟨l, hl, rfl⟩
      simp only [inv_inv, SetLike.mem_coe] at h
      exact h.1
    have hmid : ∀ c ∈ (standardComponentCA i (q ∅) : Set (rationalPoints G)),
        ∀ m ∈ K'.toSubgroup ⊓ standardLeviPoints i ν ∅, c⁻¹ * m * c ∈ K' := fun c hc m hm => by
      have hm' : m ∈ ambientConjugate c ((K ⊓ standardLeviPoints i ν ∅ :
          Subgroup (rationalPoints G)) : Set (rationalPoints G)) := by
        rw [hcon₀.1 c hc]
        exact hm
      obtain ⟨y, hy, heq⟩ := hm'
      have h : c⁻¹ * m * c = y := by
        rw [← heq]
        group
      rw [h]
      exact hy.1
    have hac : a * g = g * a := by
      rw [hgz', ha_def, ← map_mul, ← map_mul (Aubert.General.uniformizerPowers i),
        mul_comm (Multiplicative.ofAdd lam)]
    have h1 : ∀ u ∈ K', u ∈ D.N → a⁻¹ * u * a ∈ K' :=
      fun u hu huN => hlow a haplus u
        ⟨hu, standardOppositeUnipotentPoints_le_empty hG hi hν (hζ J hJ) huN⟩
    have h2 : Commute (compressedAction ρ hρ.1 K' (D.isCompact K' hKgood) a)
        (compressedAction ρ hρ.1 K' (D.isCompact K' hKgood) D.g⁻¹) := by
      have hDg : D.g⁻¹ = g := inv_inv g
      rw [hDg]
      exact compressedAction_commute_of_factor ρ hρ.1 K' _ (standardUnipotentPoints i ν ∅)
        (standardLeviPoints i ν ∅) (standardOppositeUnipotentPoints i ν ∅) hfactor hac
        (hup a haplus) (hlow a haplus) (hmid a haCA)
        (hup g hgplus₀) (hlow g hgplus₀) (hmid g hgCA₀)
    have h3 : ∀ n ∈ Fs, a * n * a⁻¹ ∈ K' := hT lam hlam hdeep
    exact hasym a h1 h2 h3
  choose T hT using hTex
  obtain ⟨T₀, hT₀⟩ := (hfinite.finite_subsets.image T).bddAbove
  exact ⟨T₀, fun lam hlam J hJ hdeep => hT J hJ lam hlam
    (fun α hα hαJ => lt_of_le_of_lt (hT₀ ⟨J, hJ, rfl⟩) (hdeep α hα hαJ))⟩

include hG hi hν hB hA hmem hζ in
open Langlands.Jacquet in
/-- **Waldspurger, Proposition I.4.3, on `Ā_0^+`.** The pairings of
`exists_uniform_standardCasselmanPairing` satisfy, for every `v` and smooth functional `ℓ`, the
asymptotic identity `ℓ(ρ(x) v) = b J (ǰ(ℓ), j(ρ(x) v))` at every point `x` of the maximal split
torus `S(F)` with `|α(x)|_F ≤ 1` for all simple roots `α` (Waldspurger's `Ā_0^+`) and every
`J ⊆ Δ` with `|α(x)|_F < ε` for all simple roots `α ∉ J`, for one `ε > 0`. -/
theorem exists_uniform_standardCasselmanPairing_dominant
    (ρ : Representation ℂ (rationalPoints G) V) (hρ : IsAdmissible ρ) :
    ∃ b : ∀ J : Set (characterLattice S),
        Coinvariants (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J) →ₗ[ℂ]
          Coinvariants ρ (standardUnipotentPoints i ν J) →ₗ[ℂ] ℂ,
      (∀ J, J ⊆ simpleRelativeRoots i ν →
        Function.Injective (b J) ∧ Function.Injective (b J).flip ∧
        ∀ (hMN : standardLeviPoints i ν J ≤
            Subgroup.normalizer (standardOppositeUnipotentPoints i ν J))
          (m : standardLeviPoints i ν J)
          (x : Coinvariants (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J))
          (y : Coinvariants ρ (standardUnipotentPoints i ν J)),
          b J (action (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J)
              (standardLeviPoints i ν J) hMN m x)
            (action ρ (standardUnipotentPoints i ν J) (standardLeviPoints i ν J)
              (standardLeviPoints_le_normalizer_standardUnipotentPoints i ν J) m y) =
            b J x y) ∧
      ∀ (v : V) (ℓ : SmoothDual ρ), ∃ ε : ℝ, 0 < ε ∧ ∀ x : rationalPoints S.toGrp,
        (∀ α ∈ simpleRelativeRoots i ν, CocharacterUniformizer.characterNorm F S α x ≤ 1) →
        ∀ J, J ⊆ simpleRelativeRoots i ν →
        (∀ α ∈ simpleRelativeRoots i ν, α ∉ J →
          CocharacterUniformizer.characterNorm F S α x < ε) →
          smoothDualPairing ρ ℓ (ρ (rationalPoints.map i x) v) =
            b J (Jacquet.mk (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J) ℓ)
              (Jacquet.mk ρ (standardUnipotentPoints i ν J) (ρ (rationalPoints.map i x) v)) := by
  obtain ⟨b, hbprop, hasym⟩ :=
    exists_uniform_standardCasselmanPairing hG hi hν hB A q hA hmem ζ hζ ρ hρ
  refine ⟨b, hbprop, fun v ℓ => ?_⟩
  have hsplit : IsSplitTorus S.toGrp := hi.isSplitSubtorus.1
  have : IsAffineHom S.toGrp.X.hom := hsplit.isAffineHom
  have : IsAffine S.X.left := isAffine_of_isAffineHom S.X.hom
  let : TopologicalSpace (rationalPoints S.toGrp) := rationalPointTopology F S.X
  let Ker := Plancherel.rationalCommonNormKernel S.toGrp
  have hKc : IsCompact (Ker : Set (rationalPoints S.toGrp)) :=
    Plancherel.SplitTorus.isCompact_commonNormKernel hsplit
  have : CompactSpace Ker := isCompact_iff_compactSpace.mp hKc
  have hloc : IsLocallyConstant (fun c : rationalPoints G => ρ c v) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro c
    obtain ⟨U, hU⟩ := hρ.1 v
    have ht : Filter.Tendsto (fun y : rationalPoints G => c⁻¹ * y) (nhds c) (nhds 1) :=
      (continuous_const.mul continuous_id :
        Continuous fun y : rationalPoints G => c⁻¹ * y).tendsto' c 1 (inv_mul_cancel c)
    filter_upwards [ht U.mem_nhds_one] with y hy
    have hyc : y = c * (c⁻¹ * y) := by group
    rw [hyc, map_mul, Module.End.mul_apply]
    congr 1
    exact (Representation.mem_invariants _ v).mp hU ⟨c⁻¹ * y, hy⟩
  have hcont : Continuous
      (fun k : Ker => rationalPoints.map i (k : rationalPoints S.toGrp)) :=
    (continuous_rationalPointMap F i.hom.hom).comp continuous_subtype_val
  have hfin : (Set.range (fun k : Ker =>
      ρ (rationalPoints.map i (k : rationalPoints S.toGrp)) v)).Finite :=
    (hloc.comp_continuous hcont).range_finite
  choose Tf hTf using fun w => hasym w ℓ
  obtain ⟨T₀, hT₀⟩ := (hfin.image Tf).bddAbove
  have hq : (1 : ℝ) < LocalField.residueCardinality F := by
    exact_mod_cast LocalField.residueCardinality_gt_one F
  refine ⟨(LocalField.residueCardinality F : ℝ) ^ (-⌈T₀⌉), zpow_pos (by linarith) _,
    fun x hdom J hJ hdeep => ?_⟩
  obtain ⟨c, hc, -⟩ := (CocharacterUniformizer.isUniformizerLatticeSection F S hsplit).2.2 x
  obtain ⟨lam, rfl⟩ := Multiplicative.ofAdd.surjective c
  let xc := CocharacterUniformizer.latticeSection F S (Multiplicative.ofAdd lam)
  let k : rationalPoints S.toGrp := x * xc⁻¹
  have hk : k ∈ Ker := hc
  have hx_eq : x = xc * k := by
    change x = xc * (x * xc⁻¹)
    rw [mul_comm x, mul_inv_cancel_left]
  have hnorm : ∀ α, CocharacterUniformizer.characterNorm F S α x =
      (LocalField.residueCardinality F : ℝ) ^ (-latticePairing S α lam) := by
    intro α
    have h1 : (Plancherel.rationalNormCharacters S.toGrp
        ((rationalCharacters.equivCharacterLattice S).symm α)).toMul k = 1 :=
      (Plancherel.mem_rationalCommonNormKernel S.toGrp k).1 hk
        ((rationalCharacters.equivCharacterLattice S).symm α)
    have h2 : CocharacterUniformizer.characterNorm F S α x =
        CocharacterUniformizer.characterNorm F S α xc := by
      simp only [CocharacterUniformizer.characterNorm]
      rw [hx_eq, map_mul, h1, mul_one]
    rw [h2]
    exact CocharacterUniformizer.characterNorm_latticeSection F S α lam
  have hlam : ∀ α ∈ simpleRelativeRoots i ν, 0 ≤ latticePairing S α lam := by
    intro α hα
    have h := hdom α hα
    rw [hnorm] at h
    by_contra hneg
    have h1 : (1 : ℝ) < (LocalField.residueCardinality F : ℝ) ^ (-latticePairing S α lam) :=
      one_lt_zpow₀ hq (by
        have : latticePairing S α lam < 0 := not_le.mp hneg
        omega)
    linarith
  let w := ρ (rationalPoints.map i k) v
  have hwT : Tf w ≤ T₀ := hT₀ ⟨w, ⟨⟨k, hk⟩, rfl⟩, rfl⟩
  have hdeep' : ∀ α ∈ simpleRelativeRoots i ν, α ∉ J → Tf w < latticePairing S α lam := by
    intro α hα hαJ
    have h := hdeep α hα hαJ
    rw [hnorm] at h
    have h' : -latticePairing S α lam < -⌈T₀⌉ := (zpow_lt_zpow_iff_right₀ hq).mp h
    have h'' : (⌈T₀⌉ : ℝ) < latticePairing S α lam := by
      exact_mod_cast (by omega : ⌈T₀⌉ < latticePairing S α lam)
    linarith [Int.le_ceil T₀]
  have key := hTf w lam hlam J hJ hdeep'
  have hpt : rationalPoints.map i x =
      Aubert.General.uniformizerPowers i (.ofAdd lam) * rationalPoints.map i k := by
    rw [hx_eq, map_mul]
    rfl
  have hρx : ρ (rationalPoints.map i x) v =
      ρ (Aubert.General.uniformizerPowers i (.ofAdd lam)) w := by
    rw [hpt, map_mul, Module.End.mul_apply]
  rw [hρx]
  exact key

include hG hi hν hB hA hmem hζ in
open Langlands.Jacquet in
/-- **Waldspurger, Proposition I.4.3** (Casselman), in the form of the source with the parabolic
subgroups `P_{m,t}`: for every `v` and smooth functional `ℓ` there is `t > 0` such that for every
`x ∈ Ā_0^+` (a point of `S(F)` with `|α(x)|_F ≤ 1` for all simple roots) the identity
`ℓ(ρ(x) v) = b J (ǰ(ℓ), j(ρ(x) v))` holds for `J = waldspurgerFace i ν t x`, the face of
`P_{x,t}`. The pairings `b J` are those of `exists_uniform_standardCasselmanPairing`. -/
theorem exists_waldspurger_uniform_asymptotics
    (ρ : Representation ℂ (rationalPoints G) V) (hρ : IsAdmissible ρ) :
    ∃ b : ∀ J : Set (characterLattice S),
        Coinvariants (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J) →ₗ[ℂ]
          Coinvariants ρ (standardUnipotentPoints i ν J) →ₗ[ℂ] ℂ,
      (∀ J, J ⊆ simpleRelativeRoots i ν →
        Function.Injective (b J) ∧ Function.Injective (b J).flip ∧
        ∀ (hMN : standardLeviPoints i ν J ≤
            Subgroup.normalizer (standardOppositeUnipotentPoints i ν J))
          (m : standardLeviPoints i ν J)
          (x : Coinvariants (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J))
          (y : Coinvariants ρ (standardUnipotentPoints i ν J)),
          b J (action (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J)
              (standardLeviPoints i ν J) hMN m x)
            (action ρ (standardUnipotentPoints i ν J) (standardLeviPoints i ν J)
              (standardLeviPoints_le_normalizer_standardUnipotentPoints i ν J) m y) =
            b J x y) ∧
      ∀ (v : V) (ℓ : SmoothDual ρ), ∃ t : ℝ, 0 < t ∧ ∀ x : rationalPoints S.toGrp,
        (∀ α ∈ simpleRelativeRoots i ν, CocharacterUniformizer.characterNorm F S α x ≤ 1) →
          smoothDualPairing ρ ℓ (ρ (rationalPoints.map i x) v) =
            b (waldspurgerFace i ν t x)
              (Jacquet.mk (smoothContragredient ρ)
                (standardOppositeUnipotentPoints i ν (waldspurgerFace i ν t x)) ℓ)
              (Jacquet.mk ρ (standardUnipotentPoints i ν (waldspurgerFace i ν t x))
                (ρ (rationalPoints.map i x) v)) := by
  obtain ⟨b, hbprop, hasym⟩ :=
    exists_uniform_standardCasselmanPairing_dominant hG hi hν hB A q hA hmem ζ hζ ρ hρ
  refine ⟨b, hbprop, fun v ℓ => ?_⟩
  obtain ⟨ε, hε, hεasym⟩ := hasym v ℓ
  have hq : (1 : ℝ) < LocalField.residueCardinality F := by
    exact_mod_cast LocalField.residueCardinality_gt_one F
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hq)
  refine ⟨(n : ℝ) + 1, by positivity, fun x hdom =>
    hεasym x hdom _ (waldspurgerFace_subset i ν _ x) fun α hα hαJ => ?_⟩
  have hlt : CocharacterUniformizer.characterNorm F S α x <
      (LocalField.residueCardinality F : ℝ) ^ (-((n : ℝ) + 1)) :=
    lt_of_not_ge fun h => hαJ ⟨hα, h⟩
  calc CocharacterUniformizer.characterNorm F S α x
      < (LocalField.residueCardinality F : ℝ) ^ (-((n : ℝ) + 1)) := hlt
    _ ≤ (LocalField.residueCardinality F : ℝ) ^ (-(n : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hq.le (by linarith)
    _ = ((LocalField.residueCardinality F : ℝ)⁻¹) ^ n := by
        rw [Real.rpow_neg (by positivity), Real.rpow_natCast, inv_pow]
    _ < ε := hn

end Uniform

section Assembly

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] standardCasselmanAssemblyIsAffine standardCasselmanAssemblyTopology
  standardCasselmanAssemblyTopologicalGroup

open Langlands.Jacquet in
/-- **Proposition I.4.3 from Renard's simultaneous basis.** If `K0` has the simultaneous standard
basis property of Renard V.5.2 (`SimultaneousStandardBasisAt`) and every face `J ⊆ Δ` has a
standard cocharacter, then the conclusion of `exists_waldspurger_uniform_asymptotics` holds for
every admissible representation. -/
theorem SimultaneousStandardBasisAt.exists_waldspurger_uniform_asymptotics
    (hG : IsConnectedReductive G)
    {i : S.toGrp ⟶ G} (hi : IsMaximalSplitTorus i) {ν : cocharacterLattice S}
    (hν : IsGenericCocharacter i ν) {K0 : Subgroup (rationalPoints G)}
    (hBasis : SimultaneousStandardBasisAt i ν K0)
    (hexists : ∀ J, J ⊆ simpleRelativeRoots i ν → ∃ ζ, IsStandardCocharacter i ν J ζ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (rationalPoints G) V) (hρ : IsAdmissible ρ) :
    ∃ b : ∀ J : Set (characterLattice S),
        Coinvariants (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J) →ₗ[ℂ]
          Coinvariants ρ (standardUnipotentPoints i ν J) →ₗ[ℂ] ℂ,
      (∀ J, J ⊆ simpleRelativeRoots i ν →
        Function.Injective (b J) ∧ Function.Injective (b J).flip ∧
        ∀ (hMN : standardLeviPoints i ν J ≤
            Subgroup.normalizer (standardOppositeUnipotentPoints i ν J))
          (m : standardLeviPoints i ν J)
          (x : Coinvariants (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J))
          (y : Coinvariants ρ (standardUnipotentPoints i ν J)),
          b J (action (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J)
              (standardLeviPoints i ν J) hMN m x)
            (action ρ (standardUnipotentPoints i ν J) (standardLeviPoints i ν J)
              (standardLeviPoints_le_normalizer_standardUnipotentPoints i ν J) m y) =
            b J x y) ∧
      ∀ (v : V) (ℓ : SmoothDual ρ), ∃ t : ℝ, 0 < t ∧ ∀ x : rationalPoints S.toGrp,
        (∀ α ∈ simpleRelativeRoots i ν, CocharacterUniformizer.characterNorm F S α x ≤ 1) →
          smoothDualPairing ρ ℓ (ρ (rationalPoints.map i x) v) =
            b (waldspurgerFace i ν t x)
              (Jacquet.mk (smoothContragredient ρ)
                (standardOppositeUnipotentPoints i ν (waldspurgerFace i ν t x)) ℓ)
              (Jacquet.mk ρ (standardUnipotentPoints i ν (waldspurgerFace i ν t x))
                (ρ (rationalPoints.map i x) v)) := by
  classical
  obtain ⟨B, hB, hBJ⟩ := hBasis
  have hdata : ∀ J : Set (characterLattice S),
      ∃ (A' : CommGroupScheme (Spec (CommRingCat.of F))) (q' : A'.toGrp ⟶ S.toGrp),
        J ⊆ simpleRelativeRoots i ν →
          IsCompatibleStandardSplitComponent i ν J A' q' ∧
            ∀ K ∈ B, StandardParabolicBasisMember i ν J q' K := by
    intro J
    by_cases hJ : J ⊆ simpleRelativeRoots i ν
    · obtain ⟨-, A', q', h1, h2⟩ := hBJ J hJ
      exact ⟨A', q', fun _ => ⟨h1, h2⟩⟩
    · exact ⟨S, 𝟙 _, fun h => absurd h hJ⟩
  choose A q hAq using hdata
  have hζex : ∀ J : Set (characterLattice S), ∃ ζ : cocharacterLattice S,
      J ⊆ simpleRelativeRoots i ν → IsStandardCocharacter i ν J ζ := by
    intro J
    by_cases hJ : J ⊆ simpleRelativeRoots i ν
    · obtain ⟨ζ, hζ⟩ := hexists J hJ
      exact ⟨ζ, fun _ => hζ⟩
    · exact ⟨0, fun h => absurd h hJ⟩
  choose ζ hζ using hζex
  exact Langlands.BruhatTits.SpecialCompact.exists_waldspurger_uniform_asymptotics hG hi hν hB
    A q (fun J hJ => (hAq J hJ).1) (fun J hJ => (hAq J hJ).2) ζ hζ ρ hρ

end Assembly

end Langlands.BruhatTits.SpecialCompact
