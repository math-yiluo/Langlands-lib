import Langlands.Representation.Exponents.ArbitraryParabolicLeviReparametrization
import Langlands.Representation.Exponents.CasselmanCentralDirections
import Langlands.Representation.Exponents.FullCenterFromSplitComponent
import Langlands.Representation.Exponents.CentralCharacterIdentityJacquet
import Langlands.Representation.Schur.RationalPoints
import Langlands.GroupScheme.Rational.ParabolicRootPresentationTransport
import Langlands.Representation.Plancherel.SplitTorusRealPartLaws
import Langlands.Representation.Geometric.SingleBlockJacquetTransport

/-! # Moving exponents between parabolics with Levi factor `M`

Helpers for the proof of Renard VII.1.3 (PDF pp.230–232). Let `Q` be a rational parabolic
whose Levi factor has source `M`, with split component `a : A ⟶ M`. For `z ∈ G(F)`, an
automorphism `ψ` of `M` and an isomorphism `e : A ≅ A'` with `e ≫ a' = a ≫ ψ`, a character
`χ' ∘ e` is an exponent along `(Q, a)` if and only if `χ'` is an exponent along
`(zQz⁻¹, ψ⁻¹ ≫ lQ, a')`, and root presentations move along with the cone transported by
`e`. Exponents only depend on the radical and Levi images. Finally, an irreducible smooth
representation of `M(F)` has a central character (Schur's lemma), and the real part of its
restriction to `A` controls unitarity.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open RealTorusSpace

variable {k : Type u} [Field k]
  {A A' : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The rational points of isomorphic commutative group schemes are isomorphic groups. -/
def splitPointsEquiv (e : A ≅ A') : rationalPoints A.toGrp ≃* rationalPoints A'.toGrp where
  toFun := rationalPoints.map (CommGroupScheme.groupHom e.hom)
  invFun := rationalPoints.map (CommGroupScheme.groupHom e.inv)
  left_inv x := by
    change rationalPoints.map (CommGroupScheme.groupHom (e.hom ≫ e.inv)) x = x
    rw [Iso.hom_inv_id]
    simp only [rationalPoints.map_apply]
    rfl
  right_inv x := by
    change rationalPoints.map (CommGroupScheme.groupHom (e.inv ≫ e.hom)) x = x
    rw [Iso.inv_hom_id]
    simp only [rationalPoints.map_apply]
    rfl
  map_mul' := (rationalPoints.map (CommGroupScheme.groupHom e.hom)).map_mul

@[simp] theorem splitPointsEquiv_apply (e : A ≅ A') (x : rationalPoints A.toGrp) :
    splitPointsEquiv e x = rationalPoints.map (CommGroupScheme.groupHom e.hom) x := rfl

theorem splitPointsEquiv_toMonoidHom (e : A ≅ A') :
    (splitPointsEquiv e).toMonoidHom = rationalPoints.map (CommGroupScheme.groupHom e.hom) :=
  rfl

/-- Restricting real characters along `f` and then along `g` is restriction along `g ≫ f`. -/
theorem rationalCharacterRestrictReal_comp_apply {G H K : GroupScheme (Spec (CommRingCat.of k))}
    (g : K ⟶ H) (f : H ⟶ G) (x : ℝ ⊗[ℤ] rationalCharacters G) :
    rationalCharacterRestrictReal g (rationalCharacterRestrictReal f x) =
      rationalCharacterRestrictReal (g ≫ f) x := by
  induction x with
  | tmul r χ =>
    simp only [rationalCharacterRestrictReal_tmul, characterRestrict_comp, AddMonoidHom.comp_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Restriction of real characters along the identity is the identity. -/
theorem rationalCharacterRestrictReal_id_apply {G : GroupScheme (Spec (CommRingCat.of k))}
    (x : ℝ ⊗[ℤ] rationalCharacters G) : rationalCharacterRestrictReal (𝟙 G) x = x := by
  induction x with
  | tmul r χ =>
    simp only [rationalCharacterRestrictReal_tmul, characterRestrict_id, AddMonoidHom.id_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

namespace ParabolicRootPresentation

variable {G M Q : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {q : Q ⟶ G} {lQ : M ⟶ Q} {a : A.toGrp ⟶ M} {a' : A'.toGrp ⟶ M}

/-- Transport of a presentation of `(q, lQ, a)` to the conjugate parabolic `q ≫ Int(z)` with
Levi `ψ⁻¹ ≫ lQ` and split component `a'`, where `e ≫ a' = a ≫ ψ`. -/
def conjugate (pres : ParabolicRootPresentation q lQ a) (z : rationalPoints G) (ψ : M ≅ M)
    (e : A ≅ A') (ha' : IsSplitComponent a')
    (he : CommGroupScheme.groupHom e.hom ≫ a' = a ≫ ψ.hom) :
    ParabolicRootPresentation (q ≫ (G.innerIso z).hom) (ψ.symm.hom ≫ lQ) a' :=
  ((pres.compAmbientIso (G.innerIso z)).leviIsoComp ψ.symm).pullbackComponent e.symm.hom ha'
    (by
      change CommGroupScheme.groupHom e.inv ≫ a ≫ ψ.hom = a'
      rw [← he, ← Category.assoc]
      change CommGroupScheme.groupHom (e.inv ≫ e.hom) ≫ a' = a'
      rw [Iso.inv_hom_id]
      exact Category.id_comp a')

/-- The positive cone of the conjugate presentation is the image of the original cone under
restriction along `e⁻¹`. -/
theorem positiveCone_conjugate [LocallyOfFiniteType G.X.hom]
    (pres : ParabolicRootPresentation q lQ a) (z : rationalPoints G) (ψ : M ≅ M)
    (e : A ≅ A') (ha' : IsSplitComponent a')
    (he : CommGroupScheme.groupHom e.hom ≫ a' = a ≫ ψ.hom) :
    (pres.conjugate z ψ e ha' he).positiveCone =
      rationalCharacterRestrictReal (CommGroupScheme.groupHom e.inv) '' pres.positiveCone := by
  rw [conjugate, ← (ParabolicRootPresentation.image_positiveCone_pullbackComponent _ e.symm ha'
    _).1, ParabolicRootPresentation.positiveCone_leviIsoComp,
    ParabolicRootPresentation.positiveCone_compAmbientIso]
  rfl

end ParabolicRootPresentation

end Langlands.GroupScheme

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

section CentralCharacter

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] {P M : GroupScheme (Spec (CommRingCat.of k))}

/-- **Schur's lemma for Levi points.** An irreducible smooth representation of `M(F)`, with
the canonical Levi topology, has a central character. -/
theorem exists_hasCentralCharacter_of_isIrreducible (l : M ⟶ P)
    (hl : IsRationalLeviSubgroup l) :
    letI := leviPointTopology l hl
    ∀ ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M), ρ.IsIrreducible →
      ∃ ω : Subgroup.center (rationalPoints M) →* ℂˣ, ρ.HasCentralCharacter ω := by
  let := leviPointTopology l hl
  intro ρ hi
  classical
  have : Nontrivial ρ := IsSimpleModule.nontrivial (MonoidAlgebra ℂ (rationalPoints M))
    ρ.representation.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : ρ)
  let T (z : Subgroup.center (rationalPoints M)) :
      ρ.representation.IntertwiningMap ρ.representation :=
    { toLinearMap := ρ.representation z
      isIntertwining' := fun g => by
        change ρ.representation (z : rationalPoints M) * ρ.representation g =
          ρ.representation g * ρ.representation (z : rationalPoints M)
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp z.property g] }
  have hs (z : Subgroup.center (rationalPoints M)) :=
    Schur.leviPoint_scalarEndomorphism k l hl ρ hi (T z)
  choose c hc _ using hs
  have act (z : Subgroup.center (rationalPoints M)) (x : ρ) :
      ρ.representation (z : rationalPoints M) x = c z • x :=
    congrArg (fun f : ρ.representation.IntertwiningMap ρ.representation => f x) (hc z)
  have c_one : c 1 = 1 := by
    apply smul_left_injective ℂ hv
    dsimp only
    rw [← act]
    simp
  have c_mul (z w : Subgroup.center (rationalPoints M)) : c (z * w) = c z * c w := by
    apply smul_left_injective ℂ hv
    dsimp only
    rw [← act]
    change ρ.representation ((z : rationalPoints M) * (w : rationalPoints M)) v = _
    rw [map_mul, Module.End.mul_apply, act, act, smul_smul]
  have c_ne (z : Subgroup.center (rationalPoints M)) : c z ≠ 0 := by
    intro hz
    have h := c_mul z⁻¹ z
    rw [inv_mul_cancel, c_one, hz, mul_zero] at h
    exact one_ne_zero h
  exact ⟨{ toFun := fun z => Units.mk0 (c z) (c_ne z)
           map_one' := Units.ext c_one
           map_mul' := fun z w => Units.ext (c_mul z w) }, act⟩

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- A split component acts on a representation with central character `ω` through the
restriction `splitComponentCentralCharacter a ha ω`. -/
theorem splitComponentCentralCharacter_smul {A : CommGroupScheme (Spec (CommRingCat.of k))}
    {a : A.toGrp ⟶ M} (ha : IsSplitComponent a) [TopologicalSpace (rationalPoints M)]
    (ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (ω : Subgroup.center (rationalPoints M) →* ℂˣ) (hω : ρ.HasCentralCharacter ω)
    (t : rationalPoints A.toGrp) (y : ρ) :
    ρ.representation (rationalPoints.map a t) y =
      (splitComponentCentralCharacter a ha ω t : ℂ) • y :=
  hω ⟨rationalPoints.map a t, ha.isCentralSplitTorus.isCentral.map_mem_center t⟩ y

/-- If the restriction of the central character `ω` of `ρ` to a split component `a` has zero
real part, then `ρ` has a unitary central character, provided the centre of `M(F)` is
compact modulo `a`. -/
theorem nonempty_unitaryCentralCharacter_of_normalizedRealPart_eq_zero (l : M ⟶ P)
    (hl : IsRationalLeviSubgroup l) {A : CommGroupScheme (Spec (CommRingCat.of k))}
    {a : A.toGrp ⟶ M} (ha : IsSplitComponent a)
    (hcpt : CenterSplitComponentCompactness M hl.isConnectedReductive A a ha)
    (ρ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (hi : letI := leviPointTopology l hl; ρ.IsIrreducible)
    (ω : Subgroup.center (rationalPoints M) →* ℂˣ)
    (hω : letI := leviPointTopology l hl; ρ.HasCentralCharacter ω)
    (hopen : @IsOpen _ (RationalPointFamily.splitComponentPointTopology ha)
      ((splitComponentCentralCharacter a ha ω).ker : Set (rationalPoints A.toGrp)))
    (h0 : Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1
      (splitComponentCentralCharacter a ha ω) = 0) :
    letI := leviPointTopology l hl
    Nonempty (UnitaryCentralCharacter ρ.representation) := by
  have := hl.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  have := ha.isAffine
  let := RationalPointFamily.splitComponentPointTopology ha
  have : Nontrivial ρ := IsSimpleModule.nontrivial (MonoidAlgebra ℂ (rationalPoints M))
    ρ.representation.asModule
  have hnorm := (Plancherel.SplitTorus.normalizedRealPart_eq_zero_iff
    ha.isCentralSplitTorus.1.1 _ hopen).mp h0
  exact ⟨unitaryCentralCharacterOfSplitComponent hl.isConnectedReductive ρ ω A a ha hcpt hω
    hnorm⟩

end CentralCharacter

section Transport

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G Q M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance exponentTransportAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (q : Q ⟶ G) (lQ : M ⟶ Q) (rQ : U ⟶ Q)
  (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
  (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
  (hmulQ : IsIso (subgroupMultiplication lQ rQ))
  {A A' : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M} {a' : A'.toGrp ⟶ M}

/-- **Reparametrizing the split component.** If `e : A ≅ A'` and `e ≫ a' = a`, then `χ' ∘ e` is
an exponent for the split component `a` exactly when `χ'` is one for `a'`. -/
theorem isNormalizedJacquetExponent_comp_splitPointsEquiv_iff (e : A ≅ A')
    (hea : CommGroupScheme.groupHom e.hom ≫ a' = a) (ha : IsSplitComponent a)
    (ha' : IsSplitComponent a') (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (χ' : rationalPoints A'.toGrp →* ℂˣ) :
    IsNormalizedJacquetExponent q lQ rQ hq hlQ hrQ hmulQ ha π
        (χ'.comp (rationalPoints.map (CommGroupScheme.groupHom e.hom))) ↔
      IsNormalizedJacquetExponent q lQ rQ hq hlQ hrQ hmulQ ha' π χ' := by
  subst hea
  rw [isNormalizedJacquetExponent_iff, isNormalizedJacquetExponent_iff]
  have hmap : splitComponentPointsMap (lQ ≫ q) (CommGroupScheme.groupHom e.hom ≫ a') =
      (splitComponentPointsMap (lQ ≫ q) a').comp (splitPointsEquiv e).toMonoidHom := by
    refine MonoidHom.ext fun t => Subtype.ext ?_
    change rationalPoints.map (lQ ≫ q)
        (rationalPoints.map (CommGroupScheme.groupHom e.hom ≫ a') t) =
      rationalPoints.map (lQ ≫ q) (rationalPoints.map a'
        (rationalPoints.map (CommGroupScheme.groupHom e.hom) t))
    rw [pointMap_comp_apply (CommGroupScheme.groupHom e.hom) a' t]
  rw [hmap, ← splitPointsEquiv_toMonoidHom, ← MonoidHom.comp_assoc]
  exact isGeneralizedEigencharacter_comp_mulEquiv_iff _ (splitPointsEquiv e) χ'

/-- **Conjugating a parabolic with Levi factor `M`.** For `z ∈ G(F)`, `ψ : M ≅ M` and
`e : A ≅ A'` with `e ≫ a' = a ≫ ψ`, the character `χ'` is an exponent along
`(q ≫ Int(z), ψ⁻¹ ≫ lQ)` with split component `a'` exactly when `χ' ∘ e` is an exponent along
`(q, lQ)` with split component `a`. -/
theorem isNormalizedJacquetExponent_conjugate_iff (z : rationalPoints G) (ψ : M ≅ M)
    (e : A ≅ A') (he : CommGroupScheme.groupHom e.hom ≫ a' = a ≫ ψ.hom)
    (hq' : IsParabolicSubgroup (q ≫ (G.innerIso z).hom))
    (hlQ' : IsRationalLeviSubgroup (ψ.symm.hom ≫ lQ))
    (hmulQ' : IsIso (subgroupMultiplication (ψ.symm.hom ≫ lQ) rQ))
    (ha : IsSplitComponent a) (ha' : IsSplitComponent a')
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) (χ' : rationalPoints A'.toGrp →* ℂˣ) :
    IsNormalizedJacquetExponent (q ≫ (G.innerIso z).hom) (ψ.symm.hom ≫ lQ) rQ hq' hlQ' hrQ
        hmulQ' ha' π χ' ↔
      IsNormalizedJacquetExponent q lQ rQ hq hlQ hrQ hmulQ ha π
        (χ'.comp (rationalPoints.map (CommGroupScheme.groupHom e.hom))) := by
  have haψ : IsSplitComponent (a ≫ ψ.symm.inv) := ha.comp_iso ψ
  rw [← isNormalizedJacquetExponent_comp_splitPointsEquiv_iff (q ≫ (G.innerIso z).hom)
    (ψ.symm.hom ≫ lQ) rQ hq' hlQ' hrQ hmulQ' e he haψ ha' π χ']
  exact isNormalizedJacquetExponent_comp_innerIso_iso_comp_iff q lQ rQ hq hlQ hrQ hmulQ z ψ.symm
    hq' hlQ' hmulQ' ha haψ π _

/-- **Exponents only depend on the Levi and radical images.** Two parabolics with the same
Levi composite and the same radical image in `G` have the same exponents. -/
theorem isNormalizedJacquetExponent_congr {Q₂ U₂ : GroupScheme (Spec (CommRingCat.of k))}
    (q₂ : Q₂ ⟶ G) (lQ₂ : M ⟶ Q₂) (rQ₂ : U₂ ⟶ Q₂) (hq₂ : IsParabolicSubgroup q₂)
    (hlQ₂ : IsRationalLeviSubgroup lQ₂) (hrQ₂ : LeviSubgroup.IsGeometricUnipotentRadical rQ₂)
    (hmulQ₂ : IsIso (subgroupMultiplication lQ₂ rQ₂))
    (hL : lQ ≫ q = lQ₂ ≫ q₂)
    (hN : SubgroupFunctor.range (rQ ≫ q) = SubgroupFunctor.range (rQ₂ ≫ q₂))
    (ha : IsSplitComponent a) (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (χ : rationalPoints A.toGrp →* ℂˣ) :
    IsNormalizedJacquetExponent q lQ rQ hq hlQ hrQ hmulQ ha π χ ↔
      IsNormalizedJacquetExponent q₂ lQ₂ rQ₂ hq₂ hlQ₂ hrQ₂ hmulQ₂ ha π χ := by
  let := RationalPointFamily.splitComponentPointTopology ha
  have eN : pointImage (rQ ≫ q) = pointImage (rQ₂ ≫ q₂) := by
    rw [pointImage_eq_range_carrier, pointImage_eq_range_carrier, hN]
  have eL : pointImage (lQ ≫ q) = pointImage (lQ₂ ≫ q₂) := by rw [hL]
  refine normalizedGeneralizedWeight_congr
    (isClosed_pointImage_comp q rQ hq.isClosedSubgroup hrQ.1.isClosedSubgroup)
    (pointImage_le_normalizer q lQ rQ hrQ)
    (isClosed_pointImage_comp q₂ rQ₂ hq₂.isClosedSubgroup hrQ₂.1.isClosedSubgroup)
    (pointImage_le_normalizer q₂ lQ₂ rQ₂ hrQ₂) π _ _
    (splitComponentPointsMap_mem_center (lQ ≫ q) ha)
    (splitComponentPointsMap_mem_center (lQ₂ ≫ q₂) ha) eN eL ?_ χ
  refine MonoidHom.ext fun t => Subtype.ext ?_
  change rationalPoints.map (lQ ≫ q) (rationalPoints.map a t) =
    rationalPoints.map (lQ₂ ≫ q₂) (rationalPoints.map a t)
  rw [hL]

section LocalField

variable [ValuativeRel k] [IsNonarchimedeanLocalField k] [LocallyOfFiniteType G.X.hom]

omit [T2Space k] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
/-- If the real part of `χ' ∘ e` misses the cone of `pres`, then the real part of `χ'` misses
the cone of the conjugate presentation. -/
theorem normalizedRealPart_notMem_positiveCone_conjugate {lQ : M ⟶ Q}
    (pres : ParabolicRootPresentation q lQ a) (ha : IsSplitComponent a)
    (z : rationalPoints G) (ψ : M ≅ M) (e : A ≅ A') (ha' : IsSplitComponent a')
    (he : CommGroupScheme.groupHom e.hom ≫ a' = a ≫ ψ.hom)
    (χ' : rationalPoints A'.toGrp →* ℂˣ)
    (hopen : @IsOpen _ (RationalPointFamily.splitComponentPointTopology ha')
      (χ'.ker : Set (rationalPoints A'.toGrp)))
    (hχ : Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1
      (χ'.comp (rationalPoints.map (CommGroupScheme.groupHom e.hom))) ∉ pres.positiveCone) :
    Plancherel.SplitTorus.normalizedRealPart ha'.isCentralSplitTorus.1.1 χ' ∉
      (pres.conjugate z ψ e ha' he).positiveCone := by
  have := ha'.isAffine
  rw [ParabolicRootPresentation.positiveCone_conjugate]
  rintro ⟨c, hc, hcx⟩
  apply hχ
  rw [Plancherel.SplitTorus.normalizedRealPart_comp_points ha.isCentralSplitTorus.1.1
    ha'.isCentralSplitTorus.1.1 e.hom χ' hopen, ← hcx,
    rationalCharacterRestrictReal_comp_apply]
  change rationalCharacterRestrictReal (CommGroupScheme.groupHom (e.hom ≫ e.inv)) c ∈ _
  rw [Iso.hom_inv_id]
  change rationalCharacterRestrictReal (𝟙 A.toGrp) c ∈ _
  rw [rationalCharacterRestrictReal_id_apply]
  exact hc

omit [LocallyOfFiniteType G.X.hom] in
/-- The real part of an exponent of a representation with unitary central character pairs to
zero with every cocharacter of the split component that is central in `G`. -/
theorem pair_normalizedRealPart_eq_zero_of_isCentral (ha : IsSplitComponent a)
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (c : UnitaryCentralCharacter π.representation) (χ : rationalPoints A.toGrp →* ℂˣ)
    (hχ : IsNormalizedJacquetExponent q lQ rQ hq hlQ hrQ hmulQ ha π χ)
    (ν : cocharacterLattice A)
    (hν : IsCentral (CommGroupScheme.groupHom ν ≫ a ≫ lQ ≫ q)) :
    RealTorusSpace.pair A (Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ)
      ((1 : ℝ) ⊗ₜ[ℤ] ν) = 0 := by
  rw [Plancherel.SplitTorus.pair_normalizedRealPart_tmul, one_mul]
  let t := CocharacterUniformizer.latticeSection k A (Multiplicative.ofAdd ν)
  obtain ⟨u, hu⟩ : ∃ u, t = rationalPoints.map (CommGroupScheme.groupHom ν) u := ⟨_, rfl⟩
  have ht : (splitComponentPointsMap (lQ ≫ q) a t : rationalPoints G) ∈
      Subgroup.center (rationalPoints G) := by
    have h := hν.map_mem_center u
    change rationalPoints.map (lQ ≫ q) (rationalPoints.map a t) ∈ _
    rwa [hu, ← pointMap_comp_apply, ← pointMap_comp_apply]
  have hnorm := normalizedJacquetExponent_norm_eq_one_of_mem_center q lQ rQ hq hlQ hrQ hmulQ ha
    π c χ hχ t ht
  have h1 : Plancherel.SplitTorus.characterNorm χ t = 1 := by
    apply Units.ext
    apply NNReal.coe_injective
    rw [Plancherel.SplitTorus.characterNorm_val]
    simpa using hnorm
  change Plancherel.normLog _ (Plancherel.SplitTorus.characterNorm χ t) = 0
  rw [h1, Plancherel.normLog_one]

end LocalField

end Transport

end Langlands.Aubert.General.RepresentedParabolic
