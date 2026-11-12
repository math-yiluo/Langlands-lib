import Langlands.BruhatTits.SpecialCompact.JacquetAdapterProof
import Langlands.Representation.Jacquet.IwahoriStablePairingAdmits
import Langlands.Representation.Jacquet.IwahoriStablePairingData
import Langlands.Representation.Jacquet.StablePairingAsymptotics
import Langlands.Representation.Jacquet.StablePairingUniformAsymptotics
import Langlands.Representation.Jacquet.StandardFixedVectorGeneration
import Langlands.Representation.Aubert.General.RationalOppositeChamber
import Langlands.Representation.Plancherel.SplitTorusCompactKernel
import Langlands.Geometry.Building.CocharacterUniformizerProof

/-! # Casselman's pairing for actual standard parabolic subgroups (Waldspurger, Théorème I.4.1)

For a connected reductive group `G` over a nonarchimedean local field, a maximal split torus, a
generic chamber cocharacter `ν`, a face `J` with a standard cocharacter, and Renard's structural
data for `P_J = M_J U_J` (a basis of compact open subgroups normal in `K₀` with the clauses of
V.5.2, and a compatible split component of `M_J`), this module builds the Library's
`StablePairingData` for `N = Ū_J`, `M = M_J`, `Nbar = U_J` and proves Waldspurger's
Théorème I.4.1 (Casselman) for every admissible representation: a nondegenerate `M_J`-invariant
pairing between the coinvariants `V̌_{Ū_J}` and `V_{U_J}` that computes matrix coefficients
`ℓ(ρ(a)v)` for every `a` in the split component with `|α(a)|_F < ε` on `Δ(P_J)`.
The identity is stated without the modulus factor; see the paired Markdown for the dictionary.
-/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.BruhatTits.SpecialCompact

section Opposite

variable {H : Type*} [Group H] [TopologicalSpace H] {K M N Nbar : Subgroup H}
  {CA CAplus CAstrict : Set H} {CAeps : ℝ → Set H}

/-- The opposite Iwahori contraction: the same basis clauses make `g⁻¹` contract the opposite
radical `Nbar`, with the factorization taken in the order `N, M, Nbar`. -/
theorem isIwahoriContraction_inv_of_contractionAndCofinality
    (hK : IsOpen (K : Set H))
    (hfactor : HasIwahoriIntersectionDecomposition K M N Nbar)
    (hcon : ContractionAndCofinality K M N Nbar CA CAplus CAstrict CAeps)
    {g : H} (hgM : g ∈ M) (hgCA : g ∈ CA)
    (hgplus : g ∈ CAplus) (hgstrict : g ∈ CAstrict) :
    Langlands.Jacquet.IsIwahoriContraction
      (⟨K, hK⟩ : OpenSubgroup H) Nbar M N g⁻¹ := by
  refine ⟨M.inv_mem hgM, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    obtain ⟨⟨l, m, n⟩, heq⟩ := hfactor.2 ⟨k⁻¹, K.inv_mem hk⟩
    have h : (l : H) * m * n = k⁻¹ := congrArg Subtype.val heq
    refine ⟨(n : H)⁻¹, ⟨K.inv_mem n.2.1, N.inv_mem n.2.2⟩, (m : H)⁻¹,
      ⟨K.inv_mem m.2.1, M.inv_mem m.2.2⟩, (l : H)⁻¹, ⟨K.inv_mem l.2.1, Nbar.inv_mem l.2.2⟩, ?_⟩
    calc k = (k⁻¹)⁻¹ := (inv_inv k).symm
      _ = ((l : H) * m * n)⁻¹ := by rw [h]
      _ = (n : H)⁻¹ * (m : H)⁻¹ * (l : H)⁻¹ := by group
  · intro u hu
    have := (hcon.2.1 g hgplus).2 ⟨u, hu, rfl⟩
    simpa only [inv_inv, SetLike.mem_coe] using this
  · intro m hm
    have hm' : g * m * g⁻¹ ∈ ambientConjugate g ((K ⊓ M : Subgroup H) : Set H) :=
      ⟨m, hm, rfl⟩
    rw [hcon.1 g hgCA] at hm'
    simpa only [inv_inv, SetLike.mem_coe] using hm'
  · intro l hl
    have := (hcon.2.1 g hgplus).1 ⟨l, hl, rfl⟩
    simpa only [inv_inv, SetLike.mem_coe] using this
  · intro x hx
    have hx' : x ∈ (Nbar : Set H) := hx
    rw [(hcon.2.2.1 g hgstrict).2] at hx'
    obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hx'
    obtain ⟨y, hy, heq⟩ := hr
    refine ⟨r, ?_⟩
    have h : g⁻¹ ^ r * x * (g⁻¹ ^ r)⁻¹ = y := by
      rw [← heq]
      group
    rw [h]
    exact hy.1
  · intro L
    let LN : OpenSubgroup N := L.comap N.subtype continuous_subtype_val
    have hbasis := (hcon.2.2.2.2.1 g hgstrict).1
    obtain ⟨s, _, hs⟩ := hbasis.2.mem_iff.mp LN.mem_nhds_one
    refine ⟨s, fun l hl => ?_⟩
    have hU : g ^ s * l * (g ^ s)⁻¹ ∈ N := hbasis.1 s ⟨l, hl, rfl⟩
    have hmem := hs (show (⟨g ^ s * l * (g ^ s)⁻¹, hU⟩ : N) ∈
      {x : N | ∃ y : N, y ∈ Subgroup.comap N.subtype K ∧
        (x : H) = g ^ s * (y : H) * (g ^ s)⁻¹} from ⟨⟨l, hl.2⟩, hl.1, rfl⟩)
    have h2 : g ^ s * l * (g ^ s)⁻¹ ∈ L := hmem
    simpa only [inv_pow, inv_inv] using h2

end Opposite

section Standard

variable {F : Type u} [Field F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

/-- The points of a compatible split component commute with the actual standard Levi. -/
theorem IsCompatibleStandardSplitComponent.map_commute {i : S.toGrp ⟶ G}
    {ν : cocharacterLattice S} {J : Set (characterLattice S)}
    {A : CommGroupScheme (Spec (CommRingCat.of F))} {q : A.toGrp ⟶ S.toGrp}
    (hA : IsCompatibleStandardSplitComponent i ν J A q) (x : rationalPoints A.toGrp)
    {m : rationalPoints G} (hm : m ∈ standardLeviPoints i ν J) :
    m * rationalPoints.map (q ≫ i) x = rationalPoints.map (q ≫ i) x * m := by
  obtain ⟨_, M, j, a, hj, _, _, ha, hcompat⟩ := hA
  rw [← hcompat]
  let e := hj.pointsEquiv (Over.mk (𝟙 (Spec (CommRingCat.of F))))
  obtain ⟨m', hm'⟩ := e.surjective ⟨m, hm⟩
  have hz : rationalPoints.map a x ∈ Subgroup.center (rationalPoints M) :=
    ha.isCentralSplitTorus.isCentral.range_le_center ⟨x, rfl⟩
  have hcomm : m' * rationalPoints.map a x = rationalPoints.map a x * m' :=
    Subgroup.mem_center_iff.1 hz m'
  have h1 : ((e m' : (standardLevi i ν J).carrier _) : rationalPoints G) = m :=
    congrArg Subtype.val hm'
  have h2 : ((e (rationalPoints.map a x) : (standardLevi i ν J).carrier _) :
      rationalPoints G) = rationalPoints.map (a ≫ j) x := by
    simp only [e, SubgroupFunctor.IsRepresentedBy.pointsEquiv_apply_coe,
      rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc]
  have h3 := congrArg (fun y => ((e y : (standardLevi i ν J).carrier _) : rationalPoints G))
    hcomm
  simp only [map_mul, Subgroup.coe_mul] at h3
  rw [h1, h2] at h3
  exact h3

/-- Reversing the chamber and the face does not change the actual standard Levi points, given a
standard cocharacter for the face. -/
theorem standardLeviPoints_neg_eq (hG : IsConnectedReductive G) {i : S.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i) {ν : cocharacterLattice S} (hν : IsGenericCocharacter i ν)
    {J : Set (characterLattice S)} {ζ : cocharacterLattice S}
    (hζ : IsStandardCocharacter i ν J ζ) :
    standardLeviPoints i (-ν) (Neg.neg '' J) = standardLeviPoints i ν J := by
  have hneg := relativeRootNegation F G hG S i hi
  have hζneg := hζ.neg i ν hneg
  have h1 := (standard_eq_dynamic_of_relativeRootNegation relativeRootNegation F G hG S i hi
    (-ν) (hν.neg i ν) _ _ hζneg).2.1
  have h2 := (standard_eq_dynamic_of_relativeRootNegation relativeRootNegation F G hG S i hi
    ν hν J ζ hζ).2.1
  rw [groupHom_neg_comp_eq_oppositeCocharacter] at h1
  have h3 : standardLevi i (-ν) (Neg.neg '' J) = standardLevi i ν J :=
    h1.trans ((Dynamic.centralizer_inverseCocharacter _).trans h2.symm)
  exact congrArg (fun H : SubgroupFunctor G => H.carrier (Over.mk (𝟙 _))) h3

/-- The actual standard Levi points normalize the actual opposite standard radical. -/
theorem standardLeviPoints_le_normalizer_standardOppositeUnipotentPoints
    (hG : IsConnectedReductive G) {i : S.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i) {ν : cocharacterLattice S} (hν : IsGenericCocharacter i ν)
    {J : Set (characterLattice S)} {ζ : cocharacterLattice S}
    (hζ : IsStandardCocharacter i ν J ζ) :
    standardLeviPoints i ν J ≤
      Subgroup.normalizer (standardOppositeUnipotentPoints i ν J) := by
  rw [← standardLeviPoints_neg_eq hG hi hν hζ]
  exact standardLeviPoints_le_normalizer_standardUnipotentPoints i (-ν) (Neg.neg '' J)

end Standard

section Pairing

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

local instance standardCasselmanIsAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance standardCasselmanTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X
local instance standardCasselmanTopologicalGroup : IsTopologicalGroup (rationalPoints G) :=
  rationalPoint_isTopologicalGroup F G

variable (hG : IsConnectedReductive G) {i : S.toGrp ⟶ G} (hi : IsMaximalSplitTorus i)
  {ν : cocharacterLattice S} (hν : IsGenericCocharacter i ν)
  {J : Set (characterLattice S)} {ζ : cocharacterLattice S}
  (hζ : IsStandardCocharacter i ν J ζ)
  {K0 : Subgroup (rationalPoints G)} {B : Set (Subgroup (rationalPoints G))}
  (hB : CompactOpenNormalBasis K0 B)
  {A : CommGroupScheme (Spec (CommRingCat.of F))} {q : A.toGrp ⟶ S.toGrp}
  (hA : IsCompatibleStandardSplitComponent i ν J A q)
  (hmem : ∀ K ∈ B, StandardParabolicBasisMember i ν J q K)

/-- A member of the basis, as an open subgroup. -/
def basisOpenSubgroup {K : Subgroup (rationalPoints G)} (hK : K ∈ B) :
    OpenSubgroup (rationalPoints G) :=
  ⟨K, (hB.1 K hK).2.2.1⟩

omit [LocallyOfFiniteType G.X.hom] in
include hB hmem in
/-- Every basis member gives both Iwahori contractions for the inverse of the chosen strict
element: `g⁻¹` contracts the opposite radical, and `g` contracts the radical. -/
theorem basis_isIwahoriContraction {K : Subgroup (rationalPoints G)} (hK : K ∈ B) :
    Langlands.Jacquet.IsIwahoriContraction (basisOpenSubgroup hB hK)
        (standardOppositeUnipotentPoints i ν J) (standardLeviPoints i ν J)
        (standardUnipotentPoints i ν J) (hA.strictElement i ν hi hζ)⁻¹ ∧
      Langlands.Jacquet.IsIwahoriContraction (basisOpenSubgroup hB hK)
        (standardUnipotentPoints i ν J) (standardLeviPoints i ν J)
        (standardOppositeUnipotentPoints i ν J) (hA.strictElement i ν hi hζ)⁻¹⁻¹ := by
  obtain ⟨hgM, hgCA, hgplus, hgstrict⟩ := hA.strictElement_spec i ν hi hζ
  refine ⟨isIwahoriContraction_inv_of_contractionAndCofinality (hB.1 K hK).2.2.1
    (hmem K hK).1 (hmem K hK).2 hgM hgCA hgplus hgstrict, ?_⟩
  rw [inv_inv]
  exact isIwahoriContraction_of_contractionAndCofinality (hB.1 K hK).2.2.1
    (hmem K hK).1 (hmem K hK).2 hgM hgCA hgplus hgstrict

omit [LocallyOfFiniteType G.X.hom] in
include hB hmem in
/-- The opposite Iwahori contraction basis of the actual standard parabolic. -/
theorem hasOppositeIwahoriContractionBasis_standard :
    Langlands.Jacquet.HasOppositeIwahoriContractionBasis
      (standardOppositeUnipotentPoints i ν J) (standardLeviPoints i ν J)
      (standardUnipotentPoints i ν J) (hA.strictElement i ν hi hζ)⁻¹ := by
  intro O hO h1
  obtain ⟨K, hK, hKO⟩ := hB.2.mem_iff.mp (hO.mem_nhds h1)
  exact ⟨basisOpenSubgroup hB hK, (hB.1 K hK).2.2.2, hKO,
    basis_isIwahoriContraction hi hζ hB hA hmem hK⟩

omit [LocallyOfFiniteType G.X.hom] in
include hA in
/-- The inverse of the chosen strict element commutes with the actual standard Levi. -/
theorem strictElement_inv_commute :
    ∀ m ∈ standardLeviPoints i ν J,
      m * (hA.strictElement i ν hi hζ)⁻¹ = (hA.strictElement i ν hi hζ)⁻¹ * m := by
  intro m hm
  obtain ⟨x, -, hx⟩ := (hA.strictElement_spec i ν hi hζ).2.1
  rw [← hx, ← map_inv]
  exact hA.map_commute x⁻¹ hm

/-- **The Casselman pairing data of an actual standard parabolic subgroup.** For the actual
standard parabolic `P_J = M_J U_J` of a connected reductive group, with opposite radical
`Ū_J`, a compact-open normal basis `B` satisfying the simultaneous basis clauses of
Renard V.5.2(ii)–(iv) for a compatible split component, and a standard cocharacter for `J`,
these are the Library's stable-pairing data with `N = Ū_J`, `Nbar = U_J`, `M = M_J` and
contracting element `g⁻¹`, where `g` is the chosen strict element of the split component. -/
def standardCasselmanPairingData : Langlands.Jacquet.StablePairingData (rationalPoints G) :=
  Langlands.Jacquet.stablePairingDataOfIwahoriContractions
    (standardOppositeUnipotentPoints i ν J) (standardLeviPoints i ν J)
    (standardUnipotentPoints i ν J)
    (standardLeviPoints_le_normalizer_standardOppositeUnipotentPoints hG hi hν hζ)
    (standardLeviPoints_le_normalizer_standardUnipotentPoints i ν J)
    (hA.strictElement i ν hi hζ)⁻¹ (strictElement_inv_commute hi hζ hA)
    (hasOppositeIwahoriContractionBasis_standard hi hζ hB hA hmem)

/-- Basis members are good subgroups of the pairing data. -/
theorem good_of_mem {K : Subgroup (rationalPoints G)} (hK : K ∈ B) :
    (standardCasselmanPairingData hG hi hν hζ hB hA hmem).Good (basisOpenSubgroup hB hK) :=
  ⟨(hB.1 K hK).2.2.2, basis_isIwahoriContraction hi hζ hB hA hmem hK⟩

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

open Langlands.Jacquet in
/-- Admissible representations satisfy the stable-pairing hypothesis `Admits` for the actual
standard pairing data. -/
theorem standardCasselmanPairingData_admits (ρ : Representation ℂ (rationalPoints G) V)
    (hρ : IsAdmissible ρ) :
    (standardCasselmanPairingData hG hi hν hζ hB hA hmem).Admits ρ hρ.1 :=
  StablePairingData.admits_of_iwahoriContractions _ ρ hρ
    (fun _ hK => hK.2.1) (fun _ hK => hK.2.2)

include hB hA hmem in
open Langlands.Jacquet in
/-- **Waldspurger, Théorème I.4.1, for actual standard parabolic subgroups**, with the
asymptotic identity on Renard's chambers `C_A^ε` of the compatible split component. For an
admissible smooth representation `ρ` of `G(F)` there is a bilinear form `b` on
`V̌_{Ū_J} × V_{U_J}`, nondegenerate on both sides and invariant under `M_J`, such that for every
`v ∈ V` and smooth functional `ℓ` there is `ε > 0` with `ℓ(ρ(a) v) = b(ǰ(ℓ), j(ρ(a) v))` for
every `a` in the image of `C_A^ε` (lattice points of `A(F)` with `|α(a)|_F < ε` for every
`α ∈ Δ(P_J)`). -/
theorem exists_standardCasselmanPairing (ρ : Representation ℂ (rationalPoints G) V)
    (hρ : IsAdmissible ρ) :
    ∃ b : Coinvariants (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J) →ₗ[ℂ]
        Coinvariants ρ (standardUnipotentPoints i ν J) →ₗ[ℂ] ℂ,
      Function.Injective b ∧ Function.Injective b.flip ∧
      (∀ (m : standardLeviPoints i ν J)
          (x : Coinvariants (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J))
          (y : Coinvariants ρ (standardUnipotentPoints i ν J)),
        b (action (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J)
            (standardLeviPoints i ν J)
            (standardLeviPoints_le_normalizer_standardOppositeUnipotentPoints hG hi hν hζ) m x)
          (action ρ (standardUnipotentPoints i ν J) (standardLeviPoints i ν J)
            (standardLeviPoints_le_normalizer_standardUnipotentPoints i ν J) m y) = b x y) ∧
      ∀ (v : V) (ℓ : SmoothDual ρ), ∃ ε : ℝ, 0 < ε ∧
        ∀ a ∈ standardComponentCAepsilon i ν J q ε,
          smoothDualPairing ρ ℓ (ρ a v) =
            b (Jacquet.mk (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J) ℓ)
              (Jacquet.mk ρ (standardUnipotentPoints i ν J) (ρ a v)) := by
  let D := standardCasselmanPairingData hG hi hν hζ hB hA hmem
  have hAd : D.Admits ρ hρ.1 := standardCasselmanPairingData_admits hG hi hν hζ hB hA hmem ρ hρ
  obtain ⟨b, hb⟩ := D.exists_isStablePairing hAd
  refine ⟨b, hb.injective hAd, hb.flip_injective hAd, hb.map_action hAd, ?_⟩
  intro v ℓ
  obtain ⟨U₁, hU₁⟩ := hρ.1 v
  obtain ⟨U₂, hU₂⟩ := isSmooth_smoothContragredient ρ ℓ
  obtain ⟨K, hKB, hKU⟩ := hB.2.mem_iff.mp (U₁ ⊓ U₂).mem_nhds_one
  have hKgood : D.Good (basisOpenSubgroup hB hKB) := good_of_mem hG hi hν hζ hB hA hmem hKB
  have hle₁ : basisOpenSubgroup hB hKB ≤ U₁ := fun x hx => (hKU hx).1
  have hle₂ : basisOpenSubgroup hB hKB ≤ U₂ := fun x hx => (hKU hx).2
  have hv := mem_fixedVectors_of_le ρ hle₁ hU₁
  have hℓ := mem_fixedVectors_of_le (smoothContragredient ρ) hle₂ hU₂
  obtain ⟨Fs, hFs, hasym⟩ :=
    hb.exists_finset_asymptotics_of_commute hAd (basisOpenSubgroup hB hKB) hKgood hv hℓ
  obtain ⟨hfac, hcon⟩ := hmem K hKB
  let Γ : Set (standardUnipotentPoints i ν J) := {x | (x : rationalPoints G) ∈ Fs}
  have hΓ : IsCompact Γ :=
    (Fs.finite_toSet.preimage Subtype.val_injective.injOn).isCompact
  obtain ⟨ε, hε, hεΓ⟩ := hcon.2.2.2.1.1 Γ hΓ
  obtain ⟨hgM, hgCA, hgplus, hgstrict⟩ := hA.strictElement_spec i ν hi hζ
  refine ⟨min ε 1, lt_min hε one_pos, fun a ha => ?_⟩
  obtain ⟨x, ⟨hxCA, hxε⟩, rfl⟩ := ha
  have haε : rationalPoints.map (q ≫ i) x ∈ standardComponentCAepsilon i ν J q ε :=
    ⟨x, ⟨hxCA, fun α hα => (hxε α hα).trans_le (min_le_left _ _)⟩, rfl⟩
  have haplus : rationalPoints.map (q ≫ i) x ∈ standardComponentCAplus i ν J q :=
    ⟨x, ⟨hxCA, fun α hα => ((hxε α hα).trans_le (min_le_right _ _)).le⟩, rfl⟩
  have haCA : rationalPoints.map (q ≫ i) x ∈ standardComponentCA i q := ⟨x, hxCA, rfl⟩
  set a := rationalPoints.map (q ≫ i) x with ha_def
  set g := hA.strictElement i ν hi hζ with hg_def
  -- the three conditions of the uniform asymptotic formula
  have hfactor : ∀ k ∈ basisOpenSubgroup hB hKB,
      ∃ l ∈ (basisOpenSubgroup hB hKB).toSubgroup ⊓ standardOppositeUnipotentPoints i ν J,
      ∃ m ∈ (basisOpenSubgroup hB hKB).toSubgroup ⊓ standardLeviPoints i ν J,
      ∃ u ∈ (basisOpenSubgroup hB hKB).toSubgroup ⊓ standardUnipotentPoints i ν J,
        k = l * m * u := by
    intro k hk
    obtain ⟨⟨l, m, n⟩, heq⟩ := hfac.2 ⟨k, hk⟩
    exact ⟨l, l.property, m, m.property, n, n.property, (congrArg Subtype.val heq).symm⟩
  have hup : ∀ c ∈ standardComponentCAplus i ν J q,
      ∀ u ∈ (basisOpenSubgroup hB hKB).toSubgroup ⊓ standardUnipotentPoints i ν J,
        c * u * c⁻¹ ∈ basisOpenSubgroup hB hKB := fun c hc u hu =>
    ((hcon.2.1 c hc).1 ⟨u, hu, rfl⟩).1
  have hlow : ∀ c ∈ standardComponentCAplus i ν J q,
      ∀ l ∈ (basisOpenSubgroup hB hKB).toSubgroup ⊓ standardOppositeUnipotentPoints i ν J,
        c⁻¹ * l * c ∈ basisOpenSubgroup hB hKB := fun c hc l hl => by
    have h := (hcon.2.1 c hc).2 ⟨l, hl, rfl⟩
    simp only [inv_inv, SetLike.mem_coe] at h
    exact h.1
  have hmid : ∀ c ∈ (standardComponentCA i q : Set (rationalPoints G)),
      ∀ m ∈ (basisOpenSubgroup hB hKB).toSubgroup ⊓ standardLeviPoints i ν J,
        c⁻¹ * m * c ∈ basisOpenSubgroup hB hKB := fun c hc m hm => by
    have hm' : m ∈ ambientConjugate c ((K ⊓ standardLeviPoints i ν J :
        Subgroup (rationalPoints G)) : Set (rationalPoints G)) := by
      rw [hcon.1 c hc]
      exact hm
    obtain ⟨y, hy, heq⟩ := hm'
    have h : c⁻¹ * m * c = y := by
      rw [← heq]
      group
    rw [h]
    exact hy.1
  have hac : a * g = g * a := by
    obtain ⟨y, -, hy⟩ := hgCA
    rw [← hy, ha_def, ← map_mul, ← map_mul, mul_comm]
  have h1 : ∀ u ∈ basisOpenSubgroup hB hKB, u ∈ D.N → a⁻¹ * u * a ∈ basisOpenSubgroup hB hKB :=
    fun u hu huN => hlow a haplus u ⟨hu, huN⟩
  have h2 : Commute (compressedAction ρ hρ.1 (basisOpenSubgroup hB hKB)
      (D.isCompact (basisOpenSubgroup hB hKB) hKgood) a)
      (compressedAction ρ hρ.1 (basisOpenSubgroup hB hKB)
        (D.isCompact (basisOpenSubgroup hB hKB) hKgood) D.g⁻¹) := by
    have hDg : D.g⁻¹ = g := inv_inv g
    rw [hDg]
    exact compressedAction_commute_of_factor ρ hρ.1 (basisOpenSubgroup hB hKB) _
      (standardUnipotentPoints i ν J) (standardLeviPoints i ν J)
      (standardOppositeUnipotentPoints i ν J) hfactor hac
      (hup a haplus) (hlow a haplus) (hmid a haCA)
      (hup g hgplus) (hlow g hgplus) (hmid g hgCA)
  have h3 : ∀ n ∈ Fs, a * n * a⁻¹ ∈ basisOpenSubgroup hB hKB := by
    intro n hn
    have hnU : n ∈ standardUnipotentPoints i ν J := hFs hn
    have hmem' := hεΓ a haε ⟨⟨n, hnU⟩, hn, rfl⟩
    obtain ⟨y, hy, heq⟩ := hmem'
    have heq' : a⁻¹ * y * a⁻¹⁻¹ = n := heq
    have h : a * n * a⁻¹ = y := by
      rw [← heq']
      group
    rw [h]
    exact hy.1
  exact hasym a h1 h2 h3

include hB hA hmem in
open Langlands.Jacquet in
/-- **Waldspurger, Théorème I.4.1, for actual standard parabolic subgroups, on the whole split
component.** The pairing of `exists_standardCasselmanPairing` satisfies the asymptotic identity
`ℓ(ρ(a) v) = b(ǰ(ℓ), j(ρ(a) v))` for every point `a` of `A(F)` (mapped into `G(F)`) with
`|α(a)|_F < ε` for all `α ∈ Δ(P_J)`, not only for the lattice points of Renard's chamber: `A(F)` is
the product of the lattice points with the compact norm kernel, which moves `v` through finitely
many vectors. -/
theorem exists_standardCasselmanPairing_splitComponent
    (ρ : Representation ℂ (rationalPoints G) V) (hρ : IsAdmissible ρ) :
    ∃ b : Coinvariants (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J) →ₗ[ℂ]
        Coinvariants ρ (standardUnipotentPoints i ν J) →ₗ[ℂ] ℂ,
      Function.Injective b ∧ Function.Injective b.flip ∧
      (∀ (m : standardLeviPoints i ν J)
          (x : Coinvariants (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J))
          (y : Coinvariants ρ (standardUnipotentPoints i ν J)),
        b (action (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J)
            (standardLeviPoints i ν J)
            (standardLeviPoints_le_normalizer_standardOppositeUnipotentPoints hG hi hν hζ) m x)
          (action ρ (standardUnipotentPoints i ν J) (standardLeviPoints i ν J)
            (standardLeviPoints_le_normalizer_standardUnipotentPoints i ν J) m y) = b x y) ∧
      ∀ (v : V) (ℓ : SmoothDual ρ), ∃ ε : ℝ, 0 < ε ∧
        ∀ x : rationalPoints A.toGrp,
          (∀ α ∈ standardParabolicComponentCharacters i ν J q,
            CocharacterUniformizer.characterNorm F A α x < ε) →
          smoothDualPairing ρ ℓ (ρ (rationalPoints.map (q ≫ i) x) v) =
            b (Jacquet.mk (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J) ℓ)
              (Jacquet.mk ρ (standardUnipotentPoints i ν J)
                (ρ (rationalPoints.map (q ≫ i) x) v)) := by
  obtain ⟨b, hinj, hinj', hinv, hasym⟩ :=
    exists_standardCasselmanPairing hG hi hν hζ hB hA hmem ρ hρ
  refine ⟨b, hinj, hinj', hinv, fun v ℓ => ?_⟩
  have hsplit : IsSplitTorus A.toGrp := hA.1.1
  have : IsAffineHom A.toGrp.X.hom := hsplit.isAffineHom
  have : IsAffine A.X.left := isAffine_of_isAffineHom A.X.hom
  let : TopologicalSpace (rationalPoints A.toGrp) := rationalPointTopology F A.X
  let Ker := Plancherel.rationalCommonNormKernel A.toGrp
  have hKc : IsCompact (Ker : Set (rationalPoints A.toGrp)) :=
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
      (fun k : Ker => rationalPoints.map (q ≫ i) (k : rationalPoints A.toGrp)) :=
    (continuous_rationalPointMap F (q ≫ i).hom.hom).comp continuous_subtype_val
  have hfin : (Set.range (fun k : Ker =>
      ρ (rationalPoints.map (q ≫ i) (k : rationalPoints A.toGrp)) v)).Finite :=
    (hloc.comp_continuous hcont).range_finite
  choose εf hεf hεasym using fun w => hasym w ℓ
  have hWne : (Set.range (fun k : Ker =>
      ρ (rationalPoints.map (q ≫ i) (k : rationalPoints A.toGrp)) v)).Nonempty :=
    ⟨_, ⟨1, rfl⟩⟩
  obtain ⟨w₀, -, hmin⟩ := Set.exists_min_image _ εf hfin hWne
  refine ⟨εf w₀, hεf w₀, fun x hx => ?_⟩
  obtain ⟨c, hc, -⟩ := (CocharacterUniformizer.isUniformizerLatticeSection F A hsplit).2.2 x
  let xc := CocharacterUniformizer.latticeSection F A c
  let k : rationalPoints A.toGrp := x * xc⁻¹
  have hk : k ∈ Ker := hc
  have hx_eq : x = xc * k := by
    change x = xc * (x * xc⁻¹)
    rw [mul_comm x, mul_inv_cancel_left]
  have hnorm : ∀ α, CocharacterUniformizer.characterNorm F A α x =
      CocharacterUniformizer.characterNorm F A α xc := by
    intro α
    have h1 : (Plancherel.rationalNormCharacters A.toGrp
        ((rationalCharacters.equivCharacterLattice A).symm α)).toMul k = 1 :=
      (Plancherel.mem_rationalCommonNormKernel A.toGrp k).1 hk
        ((rationalCharacters.equivCharacterLattice A).symm α)
    simp only [CocharacterUniformizer.characterNorm]
    rw [hx_eq, map_mul, h1, mul_one]
  let w := ρ (rationalPoints.map (q ≫ i) k) v
  have hle := hmin w ⟨⟨k, hk⟩, rfl⟩
  have hxc : rationalPoints.map (q ≫ i) xc ∈ standardComponentCAepsilon i ν J q (εf w) :=
    ⟨xc, ⟨⟨c, rfl⟩, fun α hα => ((hnorm α) ▸ hx α hα).trans_le hle⟩, rfl⟩
  have key := hεasym w _ hxc
  have hρx : ρ (rationalPoints.map (q ≫ i) x) v = ρ (rationalPoints.map (q ≫ i) xc) w := by
    rw [hx_eq, map_mul, map_mul, Module.End.mul_apply]
  rw [hρx]
  exact key

end Pairing

section Assembly

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

local instance standardCasselmanAssemblyIsAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance standardCasselmanAssemblyTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X
local instance standardCasselmanAssemblyTopologicalGroup :
    IsTopologicalGroup (rationalPoints G) :=
  rationalPoint_isTopologicalGroup F G

open Langlands.Jacquet in
/-- **Théorème I.4.1 from Renard's simultaneous basis.** If the compact open subgroup `K0` has the
simultaneous standard basis property of Renard V.5.2(i)–(iv) (`SimultaneousStandardBasisAt`), then
for every standard face `J ⊆ Δ` admitting a standard cocharacter there are a compatible split
component `q : A → S` of the standard Levi `M_J` and, for every admissible `ρ`, a pairing as in
`exists_standardCasselmanPairing_splitComponent`. -/
theorem SimultaneousStandardBasisAt.exists_casselmanPairing (hG : IsConnectedReductive G)
    {i : S.toGrp ⟶ G} (hi : IsMaximalSplitTorus i) {ν : cocharacterLattice S}
    (hν : IsGenericCocharacter i ν) {K0 : Subgroup (rationalPoints G)}
    (hBasis : SimultaneousStandardBasisAt i ν K0) {J : Set (characterLattice S)}
    (hJ : J ⊆ simpleRelativeRoots i ν) {ζ : cocharacterLattice S}
    (hζ : IsStandardCocharacter i ν J ζ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (rationalPoints G) V) (hρ : IsAdmissible ρ) :
    ∃ (A : CommGroupScheme (Spec (CommRingCat.of F))) (q : A.toGrp ⟶ S.toGrp),
      IsCompatibleStandardSplitComponent i ν J A q ∧
      ∃ b : Coinvariants (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J) →ₗ[ℂ]
          Coinvariants ρ (standardUnipotentPoints i ν J) →ₗ[ℂ] ℂ,
        Function.Injective b ∧ Function.Injective b.flip ∧
        (∀ (m : standardLeviPoints i ν J)
            (x : Coinvariants (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J))
            (y : Coinvariants ρ (standardUnipotentPoints i ν J)),
          b (action (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J)
              (standardLeviPoints i ν J)
              (standardLeviPoints_le_normalizer_standardOppositeUnipotentPoints hG hi hν hζ) m x)
            (action ρ (standardUnipotentPoints i ν J) (standardLeviPoints i ν J)
              (standardLeviPoints_le_normalizer_standardUnipotentPoints i ν J) m y) = b x y) ∧
        ∀ (v : V) (ℓ : SmoothDual ρ), ∃ ε : ℝ, 0 < ε ∧
          ∀ x : rationalPoints A.toGrp,
            (∀ α ∈ standardParabolicComponentCharacters i ν J q,
              CocharacterUniformizer.characterNorm F A α x < ε) →
            smoothDualPairing ρ ℓ (ρ (rationalPoints.map (q ≫ i) x) v) =
              b (Jacquet.mk (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J) ℓ)
                (Jacquet.mk ρ (standardUnipotentPoints i ν J)
                  (ρ (rationalPoints.map (q ≫ i) x) v)) := by
  obtain ⟨B, hB, hBJ⟩ := hBasis
  obtain ⟨-, A, q, hA, hmem⟩ := hBJ J hJ
  exact ⟨A, q, hA, exists_standardCasselmanPairing_splitComponent hG hi hν hζ hB hA hmem ρ hρ⟩

end Assembly

end Langlands.BruhatTits.SpecialCompact
