import Langlands.ClassFieldTheory.Local.ClassFormationCupLawsStatement
import Langlands.ClassFieldTheory.Local.FundamentalConsequencesProof

/-!
# Fundamental-class cup inflation laws of a finite class formation

The ordinary cup product is natural for a change of group together with
compatible coefficient maps. For local inflation this gives the unscaled cup
inflation diagrams, in every ordinary degree and in every positive Tate degree.
The inflation formula for fundamental classes then gives the scaled diagrams
`PositiveTateInflation` and `OrdinaryInflation` for every invariant family
satisfying `RelativeClassFormation`.
-/

noncomputable section

open CategoryTheory groupCohomology

namespace Langlands.Tate

universe u

set_option backward.isDefEq.respectTransparency false

variable {R G G' : Type u} [CommRing R] [Group G] [Group G']

/-- The cocycle formula for a change of group and coefficients. -/
lemma iCocycles_cocyclesMap (f : G' →* G) {A : Rep.{u} R G} {B : Rep.{u} R G'}
    (α : Rep.res f A ⟶ B) (n : ℕ) (a : cocycles A n) (x : Fin n → G') :
    iCocycles B n (cocyclesMap f α n a) x = α.hom (iCocycles A n a (f ∘ x)) := by
  have h := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i (cochainsMap f α) n) a
  exact congrFun h x

/-- The explicit cocycle cup commutes with a change of group and compatible
coefficient maps. -/
lemma ordinaryCupCocycles_map (f : G' →* G) {A B C : Rep.{u} R G}
    {A' B' C' : Rep.{u} R G'} (φ : Pairing A B C) (φ' : Pairing A' B' C')
    (α : Rep.res f A ⟶ A') (β : Rep.res f B ⟶ B') (γ : Rep.res f C ⟶ C')
    (hφ : ∀ a b, γ.hom (φ.bilinear a b) = φ'.bilinear (α.hom a) (β.hom b))
    (p q : ℕ) (a : cocycles A p) (b : cocycles B q) :
    cocyclesMap f γ (p + q) (ordinaryCupCocycles φ p q a b) =
      ordinaryCupCocycles φ' p q (cocyclesMap f α p a) (cocyclesMap f β q b) := by
  apply OrdinaryCup.cocycle_ext
  funext x
  rw [iCocycles_cocyclesMap, ordinaryCupCocycles_apply, hφ,
    ordinaryCupCocycles_apply, iCocycles_cocyclesMap, iCocycles_cocyclesMap]
  congr 1
  have hprod : f (List.ofFn fun i : Fin p => x (Fin.castAdd q i)).prod =
      (List.ofFn fun i : Fin p => (f ∘ x) (Fin.castAdd q i)).prod := by
    rw [map_list_prod, List.map_ofFn]
    rfl
  rw [← hprod]
  exact Rep.hom_comm_apply β _ _

/-- The ordinary cup commutes with a change of group and compatible coefficient
maps. -/
lemma ordinaryCup_map (f : G' →* G) {A B C : Rep.{u} R G}
    {A' B' C' : Rep.{u} R G'} (φ : Pairing A B C) (φ' : Pairing A' B' C')
    (α : Rep.res f A ⟶ A') (β : Rep.res f B ⟶ B') (γ : Rep.res f C ⟶ C')
    (hφ : ∀ a b, γ.hom (φ.bilinear a b) = φ'.bilinear (α.hom a) (β.hom b))
    (p q : ℕ) (a : groupCohomology A p) (b : groupCohomology B q) :
    groupCohomology.map f γ (p + q) (ordinaryCup φ p q a b) =
      ordinaryCup φ' p q (groupCohomology.map f α p a)
        (groupCohomology.map f β q b) := by
  obtain ⟨a, rfl⟩ := (ModuleCat.epi_iff_surjective (π A p)).mp inferInstance a
  obtain ⟨b, rfl⟩ := (ModuleCat.epi_iff_surjective (π B q)).mp inferInstance b
  rw [ordinaryCup_π_π, π_map_apply, π_map_apply, π_map_apply, ordinaryCup_π_π]
  congr 1
  exact ordinaryCupCocycles_map f φ φ' α β γ hφ p q a b

/-- Change of group commutes with transport along an equality of degrees. -/
lemma map_degree_transport (f : G' →* G) {A : Rep.{u} R G} {B : Rep.{u} R G'}
    (α : Rep.res f A ⟶ B) {m n : ℕ} (h : m = n) (y : groupCohomology A m) :
    groupCohomology.map f α n
        ((eqToIso (congrArg (groupCohomology A) h)).hom y) =
      (eqToIso (congrArg (groupCohomology B) h)).hom
        (groupCohomology.map f α m y) := by
  subst h
  rfl

end Langlands.Tate

namespace Langlands.ClassFieldTheory.Local

universe u v

section Tower

variable (K : Type v) (L M : Type u) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [Normal K L]

/-- The unit inclusion used by `relativeInflationLinear`, as a morphism of
representations along normal restriction. -/
def inflationUnitCoefficients :
    Rep.res (AlgEquiv.restrictNormalHom L : Gal(M/K) →* Gal(L/K))
      (unitsRepresentation K L) ⟶ unitsRepresentation K M :=
  Rep.ofHom
    { toLinearMap :=
        (Units.map (algebraMap L M).toMonoidHom).toAdditive.toIntLinearMap.restrictScalars
          IntegerScalars.{u}
      isIntertwining' σ := by
        ext x
        apply Units.ext
        exact AlgEquiv.restrictNormal_commutes σ L x.val }

/-- The identity coefficient map used by `integralInflation`. -/
def integralInflationCoefficients :
    Rep.res (AlgEquiv.restrictNormalHom L : Gal(M/K) →* Gal(L/K))
      (Rep.trivial IntegerScalars.{u} Gal(L/K) IntegerScalars.{u}) ⟶
        Rep.trivial IntegerScalars.{u} Gal(M/K) IntegerScalars.{u} :=
  Rep.ofHom
    { toLinearMap := LinearMap.id
      isIntertwining' _ := rfl }

theorem relativeInflationLinear_eq_map (n : ℕ) :
    relativeInflationLinear K L M n =
      (groupCohomology.map (AlgEquiv.restrictNormalHom L)
        (inflationUnitCoefficients K L M) n).hom := rfl

theorem integralInflation_eq_map (n : ℕ) :
    integralInflation K L M n =
      (groupCohomology.map (AlgEquiv.restrictNormalHom L)
        (integralInflationCoefficients K L M) n).hom := rfl

/-- Ordinary cup products commute with actual inflation, in every degree. -/
theorem ordinaryCupInflation : OrdinaryCupInflation K L M := by
  intro n c x
  simp only [relativeOrdinaryCup, LinearMap.comp_apply]
  rw [relativeInflationLinear_eq_map, relativeInflationLinear_eq_map,
    integralInflation_eq_map]
  erw [Langlands.Tate.map_degree_transport _ _ (Nat.add_comm 2 n)]
  congr 1
  exact Langlands.Tate.ordinaryCup_map (AlgEquiv.restrictNormalHom L)
    (Langlands.Tate.scalarPairing (unitsRepresentation K L))
    (Langlands.Tate.scalarPairing (unitsRepresentation K M))
    (inflationUnitCoefficients K L M) (integralInflationCoefficients K L M)
    (inflationUnitCoefficients K L M) (fun a b => map_smul _ b a) 2 n c x

variable [FiniteDimensional K L] [FiniteDimensional K M]

omit [Normal K L] [FiniteDimensional K M] in
/-- In positive degrees the ordinary-to-Tate comparison inverts the
Tate-to-ordinary comparison on the integral side. -/
theorem integralOrdinaryToTate_integralTateToOrdinary (n : ℕ) [NeZero n]
    (x : integralTateCohomology K L n) :
    integralOrdinaryToTate K L n (integralTateToOrdinary K L n x) = x := by
  have h : integralOrdinaryToTate K L n =
      (integralTateToOrdinary K L n).symm.toLinearMap := by
    let := Fintype.ofFinite Gal(L/K)
    unfold integralOrdinaryToTate integralTateToOrdinary
    rw [Langlands.Tate.ordinaryToTate_pos]
    rfl
  rw [h]
  exact (integralTateToOrdinary K L n).symm_apply_apply x

omit [Normal K L] [FiniteDimensional K M] in
/-- The Tate cup is additive in the degree-two class. -/
theorem relativeTateCup_nsmul (n : ℤ) (k : ℕ) (c : relativeCohomology K L 2) :
    relativeTateCup K L n (k • c) = k • relativeTateCup K L n c := by
  let := Fintype.ofFinite Gal(L/K)
  exact map_nsmul (Langlands.Tate.integralH2Cup (unitsRepresentation K L) n) k c

omit [Normal K L] [FiniteDimensional K M] in
/-- In positive degrees the Tate cup with a relative degree-two class is the
ordinary cup, read through the positive comparisons. -/
theorem relativeTateToOrdinary_relativeTateCup (n : ℕ) [NeZero n]
    (c : relativeCohomology K L 2) (x : integralTateCohomology K L n) :
    relativeTateToOrdinary K L (n + 2) (relativeTateCup K L n c x) =
      relativeOrdinaryCup K L n c (integralTateToOrdinary K L n x) := by
  have h := relativeOrdinaryCup_comparison K L n c (integralTateToOrdinary K L n x)
  rw [integralOrdinaryToTate_integralTateToOrdinary] at h
  rw [← h]
  exact (relativeTateToOrdinary K L (n + 2)).apply_symm_apply _

/-- Positive Tate cup products commute with actual inflation. -/
theorem positiveTateCupInflation : PositiveTateCupInflation K L M := by
  intro n _ c x
  apply (relativeTateToOrdinary K M (n + 2)).injective
  rw [relativePositiveTateInflation_comparison, relativeTateToOrdinary_relativeTateCup,
    relativeTateToOrdinary_relativeTateCup, integralPositiveTateInflation_comparison]
  exact ordinaryCupInflation K L M n c _

end Tower

namespace InvariantFamily

variable {p : ℕ} [Fact p.Prime]

/-- The finite class-formation axioms give the scaled positive Tate cup
inflation diagrams. -/
theorem positiveTateInflation_of_relativeClassFormation (I : InvariantFamily.{u,u} p)
    (hI : I.RelativeClassFormation) : I.PositiveTateInflation := by
  intro F L M _ _ _ _ _ _ _ _ _ _ c d hc hd n _ x
  have : FiniteDimensional L M := FiniteDimensional.right F.Carrier L M
  have hinf : relativeInflationLinear F.Carrier L M 2 c = Module.finrank L M • d :=
    I.fundamentalInflation_of_relativeClassFormation hI F L M c d hc hd
  rw [positiveTateCupInflation F.Carrier L M n c x, hinf, relativeTateCup_nsmul,
    LinearMap.smul_apply]

/-- The finite class-formation axioms give the scaled ordinary cup inflation
diagrams in every degree. -/
theorem ordinaryInflation_of_relativeClassFormation (I : InvariantFamily.{u,u} p)
    (hI : I.RelativeClassFormation) : I.OrdinaryInflation := by
  intro F L M _ _ _ _ _ _ _ _ _ _ c d hc hd n x
  have : FiniteDimensional L M := FiniteDimensional.right F.Carrier L M
  have hinf : relativeInflationLinear F.Carrier L M 2 c = Module.finrank L M • d :=
    I.fundamentalInflation_of_relativeClassFormation hI F L M c d hc hd
  rw [ordinaryCupInflation F.Carrier L M n c x, hinf]
  simp only [relativeOrdinaryCup, LinearMap.comp_apply, map_nsmul, LinearMap.smul_apply]

end InvariantFamily

/-- The finite class-formation axioms give the degree-scaled fundamental-class
cup inflation diagrams, in positive Tate degrees and in every ordinary degree. -/
theorem classFormationInflationLaws : ClassFormationInflationLawsStatement.{u} := by
  intro p _ I hI
  exact ⟨I.positiveTateInflation_of_relativeClassFormation hI,
    I.ordinaryInflation_of_relativeClassFormation hI⟩

end Langlands.ClassFieldTheory.Local
