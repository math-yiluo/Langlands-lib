import Langlands.Representation.Aubert.General.IwahoriNaturalJacquetDuality

/-! # The stable-lift formula for opposite normalized Jacquet duality -/

noncomputable section

open CategoryTheory

namespace Langlands.Aubert.General

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]

/-- The stable-lift formula for a natural isomorphism `Ψ : D ⋙ r_U ≅ r_O.op ⋙ D` with
respect to an element `g`: for every smooth `A` and every class `x` of the normalized
`O`-Jacquet module of `A` there is an open subgroup `W` such that, for every compact open
subgroup `K ≤ W` with Iwahori contractions for `g` in the order `(U, M, O)` and for `g⁻¹`
in the order `(O, M, U)`, some `K`-fixed vector `v` of `A` represents `x`, and `Ψ` pairs the
class of every `K`-fixed smooth functional `Λ` of `A` with `x` by `Λ(v)`. -/
def IsStableLiftDuality (U M O : Subgroup G) (hU : IsClosed (U : Set G))
    (hO : IsClosed (O : Set G)) (hMU : M ≤ Subgroup.normalizer U)
    (hMO : M ≤ Subgroup.normalizer O) (g : G)
    (Ψ : SmoothRep.contragredientFunctor.{0, uG, uV} ⋙
        normalizedJacquetFunctor.{uG, uV} U M hU hMU ≅
      (normalizedJacquetFunctor.{uG, uV} O M hO hMO).op ⋙
        SmoothRep.contragredientFunctor.{0, uG, uV}) : Prop :=
  ∀ (A : SmoothRep.{0, uG, uV} ℂ G)
    (x : (normalizedJacquetFunctor.{uG, uV} O M hO hMO).obj A),
    ∃ W : OpenSubgroup G, ∀ K : OpenSubgroup G, IsCompact (K : Set G) →
      Jacquet.IsIwahoriContraction K U M O g → Jacquet.IsIwahoriContraction K O M U g⁻¹ →
      K ≤ W → ∃ v ∈ fixedVectors A.representation K.toSubgroup,
        Jacquet.Localization.mk A.representation O 1 v = x ∧
        ∀ Λ ∈ fixedVectors (smoothContragredient A.representation) K.toSubgroup,
          smoothDualPairing
              ((normalizedJacquetFunctor.{uG, uV} O M hO hMO).obj A).representation
              (SmoothRep.hom (Ψ.hom.app (Opposite.op A))
                (Jacquet.Localization.mk (smoothContragredient A.representation) U 1 Λ)) x =
            smoothDualPairing A.representation Λ v

/-- On a smooth object satisfying the stable-pairing hypotheses `Admits` of the data built
from cofinal opposite Iwahori contractions, a stable pairing exists and induces an
isomorphism between the normalized `U`-Jacquet module of the smooth contragredient and the
smooth contragredient of the normalized `O`-Jacquet module, when the actual inverse-half
Haar characters are reciprocal. -/
theorem exists_isStablePairing_contragredient_normalizedJacquet_iso
    (U M O : Subgroup G) (hU : IsClosed (U : Set G)) (hO : IsClosed (O : Set G))
    (hMU : M ≤ Subgroup.normalizer U) (hMO : M ≤ Subgroup.normalizer O)
    (g : G) (hc : ∀ m ∈ M, m * g = g * m)
    (hBasis : Jacquet.HasOppositeIwahoriContractionBasis U M O g)
    (hχ : ∀ m : M,
      (HaarModulus.closedInverseHalfCharacter U hU M hMU m : ℂ) *
        (HaarModulus.closedInverseHalfCharacter O hO M hMO m : ℂ) = 1)
    (A : SmoothRep.{0, uG, uV} ℂ G)
    (hA : (Jacquet.stablePairingDataOfIwahoriContractions U M O hMU hMO g hc hBasis).Admits
      A.representation A.isSmooth) :
    ∃ b : Jacquet.Coinvariants (smoothContragredient A.representation) U →ₗ[ℂ]
        Jacquet.Coinvariants A.representation O →ₗ[ℂ] ℂ,
      (Jacquet.stablePairingDataOfIwahoriContractions U M O hMU hMO g hc
        hBasis).IsStablePairing A.representation A.isSmooth b ∧
      ∃ E : (normalizedJacquetFunctor.{uG, uV} U M hU hMU).obj A.contragredient ≅
          ((normalizedJacquetFunctor.{uG, uV} O M hO hMO).obj A).contragredient,
        ∀ x y, (SmoothRep.hom E.hom x).val y =
          b (Jacquet.Localization.trivialEquiv
            (smoothContragredient A.representation) U M hMU x)
            (Jacquet.Localization.trivialEquiv A.representation O M hMO y) := by
  let χU := HaarModulus.closedInverseHalfCharacter U hU M hMU
  let χO := HaarModulus.closedInverseHalfCharacter O hO M hMO
  have hχO : IsOpen (χO.ker : Set M) :=
    HaarModulus.isOpen_ker_closedInverseHalfCharacter O hO M hMO
  let D := Jacquet.stablePairingDataOfIwahoriContractions U M O hMU hMO g hc hBasis
  let Q : SmoothRep.{0, uG, uV} ℂ M :=
    SmoothRep.of (Jacquet.characterTwistedAction A.representation O M hMO χO)
      (Jacquet.isSmooth_characterTwistedAction A.representation O M hMO χO hχO A.isSmooth)
  let eO : (normalizedJacquetFunctor.{uG, uV} O M hO hMO).obj A ≅ Q :=
    SmoothRep.mkIso (twistEquiv χO (Jacquet.Localization.trivialEquiv A.representation O M hMO))
  obtain ⟨b, hb⟩ := D.exists_isStablePairing hA
  refine ⟨b, hb, ?_⟩
  obtain ⟨E, hE⟩ := hb.exists_equiv hA (ContinuousMulEquiv.refl M)
    (fun m => (χU m : ℂ)) χO hχ hχO
    ((normalizedJacquetFunctor.{uG, uV} U M hU hMU).obj A.contragredient).representation
    (Jacquet.Localization.trivialEquiv
      (smoothContragredient A.representation) U M hMU).toLinearEquiv
    (fun m x => by
      obtain ⟨v, rfl⟩ := Jacquet.Localization.mk_surjective
        (smoothContragredient A.representation) U 1 x
      change Jacquet.Localization.trivialEquiv
        (smoothContragredient A.representation) U M hMU
          ((χU m : ℂ) • Jacquet.Localization.mk
            (smoothContragredient A.representation) U 1
              (smoothContragredient A.representation m v)) = _
      rw [map_smul]
      rfl)
    Q.representation (fun _ _ => rfl)
  refine ⟨SmoothRep.mkIso E ≪≫ SmoothRep.contragredientIso eO, ?_⟩
  intro x y
  change (E x).val (Jacquet.Localization.trivialEquiv A.representation O M hMO y) = _
  exact hE x _

/-- If every smooth representation satisfies the stable-pairing hypotheses `Admits` of the
data built from cofinal opposite Iwahori contractions for `g`, and the actual inverse-half
Haar characters are reciprocal, then some natural isomorphism
`Ψ : D ⋙ r_U ≅ r_O.op ⋙ D` satisfies the stable-lift formula for `g`. -/
theorem exists_isStableLiftDuality_of_admits
    (U M O : Subgroup G) (hU : IsClosed (U : Set G)) (hO : IsClosed (O : Set G))
    (hMU : M ≤ Subgroup.normalizer U) (hMO : M ≤ Subgroup.normalizer O)
    (g : G) (hc : ∀ m ∈ M, m * g = g * m)
    (hBasis : Jacquet.HasOppositeIwahoriContractionBasis U M O g)
    (hχ : ∀ m : M,
      (HaarModulus.closedInverseHalfCharacter U hU M hMU m : ℂ) *
        (HaarModulus.closedInverseHalfCharacter O hO M hMO m : ℂ) = 1)
    (hAdm : ∀ A : SmoothRep.{0, uG, uV} ℂ G,
      (Jacquet.stablePairingDataOfIwahoriContractions U M O hMU hMO g hc hBasis).Admits
        A.representation A.isSmooth) :
    ∃ Ψ : SmoothRep.contragredientFunctor.{0, uG, uV} ⋙
        normalizedJacquetFunctor.{uG, uV} U M hU hMU ≅
      (normalizedJacquetFunctor.{uG, uV} O M hO hMO).op ⋙
        SmoothRep.contragredientFunctor.{0, uG, uV},
      IsStableLiftDuality.{uG, uV} U M O hU hO hMU hMO g Ψ := by
  let rU := normalizedJacquetFunctor.{uG, uV} U M hU hMU
  let rO := normalizedJacquetFunctor.{uG, uV} O M hO hMO
  let D := Jacquet.stablePairingDataOfIwahoriContractions U M O hMU hMO g hc hBasis
  choose b hb E hE using fun A : SmoothRep.{0, uG, uV} ℂ G =>
    exists_isStablePairing_contragredient_normalizedJacquet_iso
      U M O hU hO hMU hMO g hc hBasis hχ A (hAdm A)
  have hnat : ∀ (A B : SmoothRep.{0, uG, uV} ℂ G) (f : A ⟶ B),
      rU.map (SmoothRep.contragredientHom f) ≫ (E A).hom =
        (E B).hom ≫ SmoothRep.contragredientHom (rO.map f) := by
    intro A B f
    apply ObjectProperty.hom_ext
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    apply LinearMap.ext
    intro y
    change (SmoothRep.hom (E A).hom
        (SmoothRep.hom (rU.map (SmoothRep.contragredientHom f)) x)).val y =
      (SmoothRep.hom (E B).hom x).val (SmoothRep.hom (rO.map f) y)
    rw [hE, hE]
    obtain ⟨v, rfl⟩ := Jacquet.Localization.mk_surjective
      (smoothContragredient B.representation) U 1 x
    obtain ⟨w, rfl⟩ := Jacquet.Localization.mk_surjective A.representation O 1 y
    exact (hb A).natural (hAdm A) (hb B) (SmoothRep.hom f)
      (Jacquet.mk (smoothContragredient B.representation) U v) (Jacquet.mk A.representation O w)
  refine ⟨NatIso.ofComponents (fun A => E A.unop) (fun f => hnat _ _ f.unop), ?_⟩
  intro A x
  obtain ⟨W, hW⟩ := D.exists_open_stable_lift (hAdm A)
    (Jacquet.Localization.trivialEquiv A.representation O M hMO x)
  refine ⟨W, fun K hK hUp hLow hKW => ?_⟩
  obtain ⟨t, ht, hty⟩ := hW K ⟨hK, hUp, hLow⟩ hKW
  have hx : Jacquet.Localization.mk A.representation O 1 (t : A) = x := by
    apply (Jacquet.Localization.trivialEquiv A.representation O M hMO).toLinearEquiv.injective
    exact hty
  subst hx
  refine ⟨t, t.property, rfl, fun Λ hΛ => ?_⟩
  exact (hE A (Jacquet.Localization.mk (smoothContragredient A.representation) U 1 Λ)
    (Jacquet.Localization.mk A.representation O 1 (t : A))).trans
    (hb A K ⟨hK, hUp, hLow⟩ ⟨Λ, hΛ⟩ t ht)

/-- Fitting splittings of compression by `g` and by `g⁻¹` on the fixed vectors of every
smooth representation, for every compact open subgroup with the two opposite Iwahori
contractions, and reciprocal inverse-half Haar characters give a natural isomorphism
`Ψ : D ⋙ r_U ≅ r_O.op ⋙ D` satisfying the stable-lift formula for `g`. -/
theorem exists_isStableLiftDuality_of_splits
    (U M O : Subgroup G) (hU : IsClosed (U : Set G)) (hO : IsClosed (O : Set G))
    (hMU : M ≤ Subgroup.normalizer U) (hMO : M ≤ Subgroup.normalizer O)
    (g : G) (hc : ∀ m ∈ M, m * g = g * m)
    (hBasis : Jacquet.HasOppositeIwahoriContractionBasis U M O g)
    (hχ : ∀ m : M,
      (HaarModulus.closedInverseHalfCharacter U hU M hMU m : ℂ) *
        (HaarModulus.closedInverseHalfCharacter O hO M hMO m : ℂ) = 1)
    (hUpperSplit : ∀ (A : SmoothRep.{0, uG, uV} ℂ G) (K : OpenSubgroup G)
      (hK : IsCompact (K : Set G)), Jacquet.IsIwahoriContraction K U M O g →
        Jacquet.CompactCompressionSplits A.representation A.isSmooth K hK g)
    (hLowerSplit : ∀ (A : SmoothRep.{0, uG, uV} ℂ G) (K : OpenSubgroup G)
      (hK : IsCompact (K : Set G)), Jacquet.IsIwahoriContraction K O M U g⁻¹ →
        Jacquet.CompactCompressionSplits A.representation A.isSmooth K hK g⁻¹) :
    ∃ Ψ : SmoothRep.contragredientFunctor.{0, uG, uV} ⋙
        normalizedJacquetFunctor.{uG, uV} U M hU hMU ≅
      (normalizedJacquetFunctor.{uG, uV} O M hO hMO).op ⋙
        SmoothRep.contragredientFunctor.{0, uG, uV},
      IsStableLiftDuality.{uG, uV} U M O hU hO hMU hMO g Ψ :=
  exists_isStableLiftDuality_of_admits U M O hU hO hMU hMO g hc hBasis hχ (fun A =>
    (Jacquet.stablePairingDataOfIwahoriContractions U M O hMU hMO g hc
      hBasis).admits_of_iwahoriContractions_of_splits A.representation
      (fun _ hK => hK.2.1) (fun _ hK => hK.2.2) A.isSmooth
      (fun K hK => hUpperSplit A.contragredient K hK.1 hK.2.1)
      (fun K hK => hLowerSplit A K hK.1 hK.2.2))

end Langlands.Aubert.General
