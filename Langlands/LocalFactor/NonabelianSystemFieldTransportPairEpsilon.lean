import Langlands.LocalFactor.NonabelianSystemFieldTransportSystem
import Langlands.Correspondence.BaseLocalEuler
import Langlands.Correspondence.BlockPairEpsilon
import Langlands.Correspondence.UnramifiedReciprocityBridge
import Langlands.LocalFactor.Abelian.SelfDualTransport

/-!
# Arithmetic pair epsilon factors along an isomorphism of p-adic fields

For `g : F ≅ E` over `ℚ_p`, a local-constant system `ε` on the common closure of `E`
and its transport to `F`, an arithmetic pair epsilon certificate `(c, m)` of two
zero-monodromy classes over `F` (for the transported system and an additive
character `ψ_F`) is one of the restricted classes over `E` (for `ε` and the
character `ψ` with `ψ ∘ g = ψ_F`). Over unitary virtual Weil classes the same holds
for the multiplicity-weighted certificates.

The bottom field `σ(⊥)` of `Ē` reached from the bottom field of `F̄` is the bottom
field only propositionally. The admissible data are therefore first described over
an arbitrary intermediate field, compared at `σ(⊥)`, and then moved to the bottom
field along that equality.
-/

noncomputable section

universe u u₁ u₂ uP uV uE uW

/-! ## Unitary virtual classes along an isomorphism of local Weil groups -/

namespace Langlands.VirtualRepresentation.LocalWeil

open Langlands.Weil.Local

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u₁} p} {E : PadicField.{u₂} p}

/-- Restriction of unitary virtual Weil classes along `φ` relabels multiplicities
along the unitary basis bijection. -/
theorem restrictUnitaryLatticeEquiv_eq_equivMapDomain
    (φ : localWeilGroup E ≃ₜ* localWeilGroup F) (x : UnitaryLattice.{u₁, uV} F) :
    Weil.restrictUnitaryLatticeEquiv φ x =
      Finsupp.equivMapDomain (Weil.restrictUnitaryBasisEquiv φ) x := rfl

theorem restrictUnitaryBasisEquiv_mem_support_iff
    (φ : localWeilGroup E ≃ₜ* localWeilGroup F) (x : UnitaryLattice.{u₁, uV} F)
    (b : UnitaryBasis.{u₁, uV} F) :
    Weil.restrictUnitaryBasisEquiv φ b ∈ (Weil.restrictUnitaryLatticeEquiv φ x).support ↔
      b ∈ x.support := by
  rw [restrictUnitaryLatticeEquiv_eq_equivMapDomain, Finsupp.mem_support_iff,
    Finsupp.mem_support_iff, Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply]

/-- **Virtual arithmetic pair epsilon factors along an isomorphism of local Weil
groups.** If every basis-level arithmetic epsilon certificate over `F` gives the
same certificate for the restricted basis classes over `E`, then every virtual
certificate `(c, m)` of `x ⊗ y` over `F` is one of the restricted virtual classes
over `E`. The systems, reciprocity families and additive characters on the two
sides are arbitrary. -/
theorem isUnitaryPairEpsilonFactor_restrictUnitaryLatticeEquiv
    (φ : localWeilGroup E ≃ₜ* localWeilGroup F)
    {eF : LocalFactor.CommonClosure.ReciprocityFamily F}
    {εF : LocalFactor.NonabelianSystem.Assignment.{u₁, uP} F}
    {hεF : LocalFactor.NonabelianSystem.IsSystem F eF εF}
    {ψF : Correspondence.NontrivialAdditiveCharacter F}
    {eE : LocalFactor.CommonClosure.ReciprocityFamily E}
    {εE : LocalFactor.NonabelianSystem.Assignment.{u₂, uE} E}
    {hεE : LocalFactor.NonabelianSystem.IsSystem E eE εE}
    {ψE : Correspondence.NontrivialAdditiveCharacter E}
    (h : ∀ (a b : UnitaryBasis.{u₁, uV} F) (c : ℂˣ) (m : ℤ),
      Correspondence.IsArithmeticPairEpsilonFactor F eF εF hεF ψF
          (unitaryBasisPairClass F a) (unitaryBasisPairClass F b) c m →
        Correspondence.IsArithmeticPairEpsilonFactor E eE εE hεE ψE
          (unitaryBasisPairClass E (Weil.restrictUnitaryBasisEquiv φ a))
          (unitaryBasisPairClass E (Weil.restrictUnitaryBasisEquiv φ b)) c m)
    {x y : UnitaryLattice.{u₁, uV} F} {e : ℂˣ × ℤ}
    (hxy : IsUnitaryPairEpsilonFactor F eF εF hεF ψF x y e) :
    IsUnitaryPairEpsilonFactor E eE εE hεE ψE (Weil.restrictUnitaryLatticeEquiv φ x)
      (Weil.restrictUnitaryLatticeEquiv φ y) e := by
  set u := Weil.restrictUnitaryBasisEquiv.{u₂, u₁, uV} φ with hu
  obtain ⟨c, hc, rfl⟩ := hxy
  refine ⟨fun a b => c (u.symm a) (u.symm b), fun a ha b hb => ?_, ?_⟩
  · rw [← u.apply_symm_apply a, restrictUnitaryBasisEquiv_mem_support_iff] at ha
    rw [← u.apply_symm_apply b, restrictUnitaryBasisEquiv_mem_support_iff] at hb
    have h' := h (u.symm a) (u.symm b) _ _ (hc _ ha _ hb)
    rwa [u.apply_symm_apply, u.apply_symm_apply] at h'
  · simp only [restrictUnitaryLatticeEquiv_eq_equivMapDomain, Finsupp.prod_equivMapDomain,
      Finsupp.sum_equivMapDomain, hu, Equiv.symm_apply_apply]

end Langlands.VirtualRepresentation.LocalWeil

namespace Langlands.LocalFactor.NonabelianSystem.FieldTransport

open LocalClassField Weil.Local CommonClosure VirtualRepresentation

/-! ## Admissible bottom-field data over an arbitrary intermediate field -/

section Generic

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{u} p)

local instance : TopologicalSpace K.Carrier := K.canonicalTopologicalData.topology

/-- `ψ'` agrees with `ψ` on the image of `K` in the intermediate field `L`. Over the
bottom field this is `Correspondence.IsBaseCharacter`. -/
def IsImageCharacter (L : Extension K) (ψ : Correspondence.NontrivialAdditiveCharacter K)
    (ψ' : AdditiveCharacter K L) : Prop :=
  letI := (fieldData K L).topology
  ∀ y : K.Carrier,
    ψ'.toAddChar (⟨algebraMap K.Carrier (AlgebraicClosure K.Carrier) y,
      L.field.algebraMap_mem y⟩ : L.field) = ψ.toAddChar y

/-- `A` is a pair over `L` equivalent to the restriction of a representative of `X`
to the subgroup fixing `L`. Over the bottom field this is
`Correspondence.IsBaseRestriction`. -/
def IsRestrictionDatum (L : Extension K) (X : Correspondence.LocalPairClass.{u, uP} K)
    (A : CommonClosureWeilDeligne.Pair.{u, uV} K L) : Prop :=
  ∃ B : LocalWeilDeligneRepresentation.{u, uP} K,
    WeilDeligneRepresentation.classOf B = X ∧
      Nonempty (WeilDeligneRepresentation.Equiv
        (WeilDeligneRepresentation.restrict (weilSubgroup K L).subtype B) A)

/-- The data clause and the value clause of `Correspondence.IsArithmeticPairEpsilonFactor`,
with the bottom field replaced by an arbitrary intermediate field `L`. -/
def IsEpsilonFactorAt (eC : ReciprocityFamily K) (ε : Assignment.{u, uV} K)
    (hε : IsSystem K eC ε) (L : Extension K) (ψ : Correspondence.NontrivialAdditiveCharacter K)
    (X Y : Correspondence.LocalPairClass.{u, uP} K) (c : ℂˣ) (m : ℤ) : Prop :=
  (∃ (ψ' : AdditiveCharacter K L) (μ : HaarMeasure K L)
      (A B : CommonClosureWeilDeligne.Pair.{u, uV} K L),
    IsImageCharacter K L ψ ψ' ∧ CommonClosureSpectral.IsSelfDual K L ψ' μ ∧
      IsRestrictionDatum K L X A ∧ IsRestrictionDatum K L Y B ∧
        A.toFiniteRepresentation.IsContinuous ∧ B.toFiniteRepresentation.IsContinuous) ∧
  ∀ (ψ' : AdditiveCharacter K L) (μ : HaarMeasure K L)
    (A B : CommonClosureWeilDeligne.Pair.{u, uV} K L),
    IsImageCharacter K L ψ ψ' → CommonClosureSpectral.IsSelfDual K L ψ' μ →
    IsRestrictionDatum K L X A → IsRestrictionDatum K L Y B →
    ∀ (hA : A.toFiniteRepresentation.IsContinuous) (hB : B.toFiniteRepresentation.IsContinuous)
      (Φ : CommonClosureWeilDeligne.GeometricFrobenius K L) (s : ℂ),
      (CommonClosureGamma.conditionalPairEpsilonValue K eC ε hε L ψ' μ A B hA hB Φ s : ℂ) =
        RankinSelberg.epsilonMonomial K.canonicalTopologicalData.residueCardinality c m s

theorem isBaseCharacter_iff_isImageCharacter (ψ : Correspondence.NontrivialAdditiveCharacter K)
    (ψ' : AdditiveCharacter K (Correspondence.baseExtension K)) :
    Correspondence.IsBaseCharacter K ψ ψ' ↔
      IsImageCharacter K (Correspondence.baseExtension K) ψ ψ' := by
  constructor
  · intro h y
    refine (h _).trans ?_
    exact congrArg ψ.toAddChar
      (IntermediateField.botEquiv_def (E := AlgebraicClosure K.Carrier) y)
  · intro h x
    set y := IntermediateField.botEquiv K.Carrier (AlgebraicClosure K.Carrier) x with hy
    have hx : x = (⟨algebraMap K.Carrier (AlgebraicClosure K.Carrier) y,
        (Correspondence.baseExtension K).field.algebraMap_mem y⟩ :
          (Correspondence.baseExtension K).field) :=
      ((IntermediateField.botEquiv K.Carrier (AlgebraicClosure K.Carrier)).symm_apply_apply
        x).symm.trans (IntermediateField.botEquiv_symm (E := AlgebraicClosure K.Carrier) y)
    rw [hx]
    exact h y

/-- The arithmetic pair epsilon factor is the data and value clauses over the bottom
field together with the existence of a geometric Frobenius there. -/
theorem isArithmeticPairEpsilonFactor_iff (eC : ReciprocityFamily K) (ε : Assignment.{u, uV} K)
    (hε : IsSystem K eC ε) (ψ : Correspondence.NontrivialAdditiveCharacter K)
    (X Y : Correspondence.LocalPairClass.{u, uP} K) (c : ℂˣ) (m : ℤ) :
    Correspondence.IsArithmeticPairEpsilonFactor K eC ε hε ψ X Y c m ↔
      IsEpsilonFactorAt K eC ε hε (Correspondence.baseExtension K) ψ X Y c m ∧
        Nonempty (CommonClosureWeilDeligne.GeometricFrobenius K
          (Correspondence.baseExtension K)) := by
  constructor
  · rintro ⟨⟨ψ', μ, A, B, ⟨hψ, hμ, hA, hB⟩, hAc, hBc⟩, hΦ, hval⟩
    refine ⟨⟨⟨ψ', μ, A, B, (isBaseCharacter_iff_isImageCharacter K ψ ψ').1 hψ, hμ, hA, hB,
      hAc, hBc⟩, ?_⟩, hΦ⟩
    intro ψ' μ A B hψ hμ hA hB
    exact hval ψ' μ A B ⟨(isBaseCharacter_iff_isImageCharacter K ψ ψ').2 hψ, hμ, hA, hB⟩
  · rintro ⟨⟨⟨ψ', μ, A, B, hψ, hμ, hA, hB, hAc, hBc⟩, hval⟩, hΦ⟩
    refine ⟨⟨ψ', μ, A, B, ⟨(isBaseCharacter_iff_isImageCharacter K ψ ψ').2 hψ, hμ, hA, hB⟩,
      hAc, hBc⟩, hΦ, ?_⟩
    rintro ψ' μ A B ⟨hψ, hμ, hA, hB⟩
    exact hval ψ' μ A B ((isBaseCharacter_iff_isImageCharacter K ψ ψ').1 hψ) hμ hA hB

/-- A restriction datum of a class is equivalent to the restriction of every
representative of the class. -/
theorem IsRestrictionDatum.nonempty_equiv {L : Extension K}
    {X : Correspondence.LocalPairClass.{u, uP} K}
    {V : LocalWeilDeligneRepresentation.{u, uP} K} (hV : WeilDeligneRepresentation.classOf V = X)
    {A : CommonClosureWeilDeligne.Pair.{u, uV} K L} (h : IsRestrictionDatum K L X A) :
    Nonempty (WeilDeligneRepresentation.Equiv
      (WeilDeligneRepresentation.restrict (weilSubgroup K L).subtype V) A) := by
  obtain ⟨B, hB, ⟨f⟩⟩ := h
  obtain ⟨e⟩ := (WeilDeligneRepresentation.classOf_eq_iff V B).1 (hV.trans hB.symm)
  exact ⟨(WeilDeligneRepresentation.restrictEquiv _ e).trans f⟩

end Generic

/-! ## Comparison at `σ(⊥)` -/

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u₁} p) (E : PadicField.{u₂} p)
  (g : F.Carrier ≃ₐ[Padic p] E.Carrier)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : TopologicalSpace E.Carrier := E.canonicalTopologicalData.topology

/-- `σ(⊥) = ⊥` as finite intermediate fields of `Ē`. -/
theorem mapExtension_baseExtension :
    mapExtension F E g (Correspondence.baseExtension F) = Correspondence.baseExtension E :=
  Subtype.ext (mapField_bot F E g (Correspondence.baseExtension F) rfl)

/-- The transported character agrees with `ψ` on the image of `E` when the original
one agrees with `ψ_F = ψ ∘ g` on the image of `F`. -/
theorem isImageCharacter_additiveCharacterMap (L : Extension F)
    {ψF : Correspondence.NontrivialAdditiveCharacter F}
    {ψ : Correspondence.NontrivialAdditiveCharacter E} (hψ : ∀ x : F.Carrier, ψ (g x) = ψF x)
    {ψ' : AdditiveCharacter F L} (h : IsImageCharacter F L ψF ψ') :
    IsImageCharacter E (mapExtension F E g L) ψ (additiveCharacterMap F E g L ψ') := by
  intro y
  have hy : (mapFieldRingEquiv F E g L).symm
      (⟨algebraMap E.Carrier (AlgebraicClosure E.Carrier) y,
        (mapExtension F E g L).field.algebraMap_mem y⟩ : (mapExtension F E g L).field) =
      (⟨algebraMap F.Carrier (AlgebraicClosure F.Carrier) (g.symm y),
        L.field.algebraMap_mem (g.symm y)⟩ : L.field) :=
    Subtype.ext (closureEquiv_symm_algebraMap F E g y)
  let := (fieldData F L).topology
  change ψ'.toAddChar ((mapFieldRingEquiv F E g L).symm _) = _
  rw [hy, h (g.symm y), ← hψ (g.symm y), AlgEquiv.apply_symm_apply]

/-- On `σ(⊥)` a character agreeing with `ψ` on the image of `E` is the transported
character. -/
theorem additiveCharacterMap_eq_of_isImageCharacter
    {ψF : Correspondence.NontrivialAdditiveCharacter F}
    {ψ : Correspondence.NontrivialAdditiveCharacter E} (hψ : ∀ x : F.Carrier, ψ (g x) = ψF x)
    {ψ' : AdditiveCharacter F (Correspondence.baseExtension F)}
    (h : IsImageCharacter F (Correspondence.baseExtension F) ψF ψ')
    {ψE : AdditiveCharacter E (mapExtension F E g (Correspondence.baseExtension F))}
    (hE : IsImageCharacter E (mapExtension F E g (Correspondence.baseExtension F)) ψ ψE) :
    additiveCharacterMap F E g (Correspondence.baseExtension F) ψ' = ψE := by
  have h' := isImageCharacter_additiveCharacterMap F E g (Correspondence.baseExtension F) hψ h
  let := (fieldData E (mapExtension F E g (Correspondence.baseExtension F))).topology
  apply HarmonicAnalysis.UnitaryAdditiveCharacter.ext
  intro z
  have hz : (z : AlgebraicClosure E.Carrier) ∈
      (⊥ : IntermediateField E.Carrier (AlgebraicClosure E.Carrier)) := by
    rw [← mapField_bot F E g (Correspondence.baseExtension F) rfl]
    exact z.2
  obtain ⟨y, hy⟩ := IntermediateField.mem_bot.1 hz
  have hz' : (⟨algebraMap E.Carrier (AlgebraicClosure E.Carrier) y,
      (mapExtension F E g (Correspondence.baseExtension F)).field.algebraMap_mem y⟩ :
        (mapExtension F E g (Correspondence.baseExtension F)).field) = z :=
    Subtype.ext hy
  rw [← hz']
  exact (h' y).trans (hE y).symm

/-- Self-duality is preserved and reflected by the transported character and measure. -/
theorem isSelfDual_map_iff (L : Extension F) (ψ' : AdditiveCharacter F L) (μ : HaarMeasure F L) :
    CommonClosureSpectral.IsSelfDual E (mapExtension F E g L) (additiveCharacterMap F E g L ψ')
        (haarMeasureMap F E g L μ) ↔
      CommonClosureSpectral.IsSelfDual F L ψ' μ :=
  PadicField.AbelianTransport.isSelfDual_iff (L.asPadicField (p := p))
    ((mapExtension F E g L).asPadicField (p := p)) (fieldEquiv F E g L) ψ' μ

/-- Every measure of `σ(L)` self-dual for the transported character is the
pushforward of a measure of `L` self-dual for the original one. -/
theorem exists_haarMeasureMap_eq (L : Extension F) (ψ' : AdditiveCharacter F L)
    (ν : HaarMeasure E (mapExtension F E g L))
    (hν : CommonClosureSpectral.IsSelfDual E (mapExtension F E g L)
      (additiveCharacterMap F E g L ψ') ν) :
    ∃ μ : HaarMeasure F L, CommonClosureSpectral.IsSelfDual F L ψ' μ ∧
      haarMeasureMap F E g L μ = ν := by
  let e := PadicField.AbelianTransport.selfDualHaarEquiv (L.asPadicField (p := p))
    ((mapExtension F E g L).asPadicField (p := p)) (fieldEquiv F E g L) ψ'
  exact ⟨Subtype.val (e.symm (Subtype.mk ν hν)), Subtype.property (e.symm (Subtype.mk ν hν)),
    congrArg Subtype.val (e.apply_symm_apply (Subtype.mk ν hν))⟩

/-- Restricting along `W_E(σ(L)) ≅ W_F(L)` the restriction of `V` to `W_F(L)` is
restricting to `W_E(σ(L))` the restriction of `V` along `W_E ≅ W_F`. -/
def restrictRestrictEquiv (L : Extension F) (V : LocalWeilRepresentation.{u₁, uW} F) :
    FiniteRepresentation.Equiv
      (FiniteRepresentation.restrict (subgroupWeilEquiv F E g L : _ →ₜ* weilSubgroup F L).toMonoidHom
        (FiniteRepresentation.restrict (weilSubgroup F L).subtype V))
      (FiniteRepresentation.restrict (weilSubgroup E (mapExtension F E g L)).subtype
        (FiniteRepresentation.restrict
          (weilEquiv F E g : localWeilGroup E →ₜ* localWeilGroup F).toMonoidHom V)) where
  toLinearEquiv := LinearEquiv.refl ℂ _
  isIntertwining' _ := rfl

/-- Restriction data of `V` over `L` and of its restriction along `W_E ≅ W_F` over
`σ(L)` correspond under restriction along `W_E(σ(L)) ≅ W_F(L)`. -/
def datumEquiv {L : Extension F} {V : LocalWeilRepresentation.{u₁, uW} F}
    {A : CommonClosureWeilDeligne.Pair.{u₁, uE} F L}
    {A' : CommonClosureWeilDeligne.Pair.{u₂, uE} E (mapExtension F E g L)}
    (f : WeilDeligneRepresentation.Equiv
      (WeilDeligneRepresentation.restrict (weilSubgroup F L).subtype
        (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter F).toMonoidHom V)) A)
    (f' : WeilDeligneRepresentation.Equiv
      (WeilDeligneRepresentation.restrict (weilSubgroup E (mapExtension F E g L)).subtype
        (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter E).toMonoidHom
          (FiniteRepresentation.restrict
            (weilEquiv F E g : localWeilGroup E →ₜ* localWeilGroup F).toMonoidHom V))) A') :
    FiniteRepresentation.Equiv
      (FiniteRepresentation.restrict (subgroupWeilEquiv F E g L : _ →ₜ* weilSubgroup F L).toMonoidHom
        A.toFiniteRepresentation) A'.toFiniteRepresentation :=
  ((FiniteRepresentation.restrictEquivOfEquiv _ f.representationEquiv).symm.trans
    (restrictRestrictEquiv F E g L V)).trans f'.representationEquiv

/-- The pair over `σ(L)` with zero monodromy whose representation is a model of the
restriction of `A` along `W_E(σ(L)) ≅ W_F(L)`. -/
def transportPair (L : Extension F) (A : CommonClosureWeilDeligne.Pair.{u₁, uE} F L) :
    CommonClosureWeilDeligne.Pair.{u₂, uE} E (mapExtension F E g L) :=
  WeilDeligneRepresentation.zeroMonodromy
    (CommonClosureWeilDeligne.normCharacter E (mapExtension F E g L)).toMonoidHom
    (FiniteRepresentation.universeModel
      (FiniteRepresentation.restrict
        (subgroupWeilEquiv F E g L : _ →ₜ* weilSubgroup F L).toMonoidHom
        A.toFiniteRepresentation))

theorem isContinuous_transportPair (L : Extension F)
    {A : CommonClosureWeilDeligne.Pair.{u₁, uE} F L} (hA : A.toFiniteRepresentation.IsContinuous) :
    (transportPair F E g L A).toFiniteRepresentation.IsContinuous :=
  (FiniteRepresentation.isContinuous_iff_of_equiv (FiniteRepresentation.universeModelEquiv _)).mp
    (FiniteRepresentation.isContinuous_restrict _ (subgroupWeilEquiv F E g L).continuous hA)

theorem isRestrictionDatum_transportPair {L : Extension F} {V : LocalWeilRepresentation.{u₁, uW} F}
    {A : CommonClosureWeilDeligne.Pair.{u₁, uE} F L}
    (f : WeilDeligneRepresentation.Equiv
      (WeilDeligneRepresentation.restrict (weilSubgroup F L).subtype
        (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter F).toMonoidHom V)) A) :
    IsRestrictionDatum E (mapExtension F E g L)
      (WeilDeligneRepresentation.classOf
        (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter E).toMonoidHom
          (FiniteRepresentation.restrict
            (weilEquiv F E g : localWeilGroup E →ₜ* localWeilGroup F).toMonoidHom V)))
      (transportPair F E g L A) :=
  ⟨_, rfl, ⟨WeilDeligneRepresentation.zeroMonodromyEquivOfEquiv _ rfl rfl
    (((restrictRestrictEquiv F E g L V).symm.trans
      (FiniteRepresentation.restrictEquivOfEquiv _ f.representationEquiv)).trans
        (FiniteRepresentation.universeModelEquiv _))⟩⟩

/-- **The comparison at `σ(⊥)`.** An arithmetic certificate of two zero-monodromy
classes over the bottom field of `F̄`, for the transported system and `ψ_F`, gives
the data and value clauses over `σ(⊥)` for the restricted classes, `ε` and `ψ`. -/
theorem isEpsilonFactorAt_transport (eE : ReciprocityFamily E) (ε : Assignment.{u₂, uE} E)
    (hε : IsSystem E eE ε)
    (hε' : IsSystem F (transportFamily F E g eE) (transportAssignment F E g ε))
    (ψF : Correspondence.NontrivialAdditiveCharacter F)
    (ψ : Correspondence.NontrivialAdditiveCharacter E) (hψ : ∀ x : F.Carrier, ψ (g x) = ψF x)
    (V W : LocalWeilRepresentation.{u₁, uW} F) (c : ℂˣ) (m : ℤ)
    (h : IsEpsilonFactorAt F (transportFamily F E g eE) (transportAssignment F E g ε) hε'
      (Correspondence.baseExtension F) ψF
      (WeilDeligneRepresentation.classOf
        (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter F).toMonoidHom V))
      (WeilDeligneRepresentation.classOf
        (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter F).toMonoidHom W)) c m) :
    IsEpsilonFactorAt E eE ε hε (mapExtension F E g (Correspondence.baseExtension F)) ψ
      (WeilDeligneRepresentation.classOf
        (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter E).toMonoidHom
          (FiniteRepresentation.restrict
            (weilEquiv F E g : localWeilGroup E →ₜ* localWeilGroup F).toMonoidHom V)))
      (WeilDeligneRepresentation.classOf
        (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter E).toMonoidHom
          (FiniteRepresentation.restrict
            (weilEquiv F E g : localWeilGroup E →ₜ* localWeilGroup F).toMonoidHom W))) c m := by
  obtain ⟨⟨ψ'F, μ₀, AF, BF, hψ'F, hμ₀, hAF, hBF, hAFc, hBFc⟩, hval⟩ := h
  obtain ⟨fAF⟩ := IsRestrictionDatum.nonempty_equiv F rfl hAF
  obtain ⟨fBF⟩ := IsRestrictionDatum.nonempty_equiv F rfl hBF
  refine ⟨⟨additiveCharacterMap F E g _ ψ'F, haarMeasureMap F E g _ μ₀,
    transportPair F E g _ AF, transportPair F E g _ BF,
    isImageCharacter_additiveCharacterMap F E g _ hψ hψ'F,
    (isSelfDual_map_iff F E g _ ψ'F μ₀).2 hμ₀,
    isRestrictionDatum_transportPair F E g fAF, isRestrictionDatum_transportPair F E g fBF,
    isContinuous_transportPair F E g _ hAFc, isContinuous_transportPair F E g _ hBFc⟩, ?_⟩
  intro ψ'E μE AE BE hψ'E hμE hAE hBE hAEc hBEc Φ s
  obtain rfl := additiveCharacterMap_eq_of_isImageCharacter F E g hψ hψ'F hψ'E
  obtain ⟨μF, hμF, rfl⟩ := exists_haarMeasureMap_eq F E g _ ψ'F μE hμE
  obtain ⟨fAE⟩ := IsRestrictionDatum.nonempty_equiv E rfl hAE
  obtain ⟨fBE⟩ := IsRestrictionDatum.nonempty_equiv E rfl hBE
  have hNF := WeilDeligneRepresentation.tensor_monodromy_eq_zero
    (WeilDeligneRepresentation.monodromy_eq_zero_of_equiv fAF rfl)
    (WeilDeligneRepresentation.monodromy_eq_zero_of_equiv fBF rfl)
  have hNE := WeilDeligneRepresentation.tensor_monodromy_eq_zero
    (WeilDeligneRepresentation.monodromy_eq_zero_of_equiv fAE rfl)
    (WeilDeligneRepresentation.monodromy_eq_zero_of_equiv fBE rfl)
  have hclass : virtualMap F E g (Correspondence.baseExtension F)
      (CommonClosureWeilDeligne.underlyingClass F (Correspondence.baseExtension F)
        (WeilDeligneRepresentation.tensor AF BF)
        (CommonClosureGamma.tensor_isContinuous F _ AF BF hAFc hBFc)) =
      CommonClosureWeilDeligne.underlyingClass E (mapExtension F E g (Correspondence.baseExtension F))
        (WeilDeligneRepresentation.tensor AE BE)
        (CommonClosureGamma.tensor_isContinuous E _ AE BE hAEc hBEc) :=
    virtualMap_ofRepresentation F E g _ _ _
      ((FiniteRepresentation.restrictTensorIdEquiv _ _ _).trans
        (FiniteRepresentation.tensorEquivOfEquiv (datumEquiv F E g fAF fAE)
          (datumEquiv F E g fBF fBE)))
  have hF := hval ψ'F μF AF BF hψ'F hμF hAF hBF hAFc hBFc
    (Correspondence.baseGeometricFrobenius F) s
  rw [PadicField.CanonicalTransport.residueCardinality_eq F E g, ← hF]
  congr 1
  refine (CommonClosureWeilDeligne.conditionalEpsilonValue_of_monodromy_zero E eE ε hε _ _ _ _ _
    hNE Φ s).trans (Eq.trans ?_ (CommonClosureWeilDeligne.conditionalEpsilonValue_of_monodromy_zero
      F _ _ hε' _ _ _ _ _ hNF (Correspondence.baseGeometricFrobenius F) s).symm)
  rw [CommonClosureSpectral.conditionalDeligneValue, CommonClosureSpectral.conditionalDeligneValue,
    transportAssignment_apply, virtualMap_virtualTwist]
  exact congrArg (fun x => ε _ (additiveCharacterMap F E g _ ψ'F) (haarMeasureMap F E g _ μF)
    (CommonClosureSpectral.virtualTwist E _ s x)) hclass.symm

/-! ## The bottom field and unitary classes -/

/-- **Arithmetic pair epsilon factors of zero-monodromy classes along `g`.** -/
theorem isArithmeticPairEpsilonFactor_zeroMonodromy_transport (eE : ReciprocityFamily E)
    (ε : Assignment.{u₂, uE} E) (hε : IsSystem E eE ε)
    (hε' : IsSystem F (transportFamily F E g eE) (transportAssignment F E g ε))
    (ψF : Correspondence.NontrivialAdditiveCharacter F)
    (ψ : Correspondence.NontrivialAdditiveCharacter E) (hψ : ∀ x : F.Carrier, ψ (g x) = ψF x)
    (V W : LocalWeilRepresentation.{u₁, uW} F) (c : ℂˣ) (m : ℤ)
    (h : Correspondence.IsArithmeticPairEpsilonFactor F (transportFamily F E g eE)
      (transportAssignment F E g ε) hε' ψF
      (WeilDeligneRepresentation.classOf
        (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter F).toMonoidHom V))
      (WeilDeligneRepresentation.classOf
        (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter F).toMonoidHom W)) c m) :
    Correspondence.IsArithmeticPairEpsilonFactor E eE ε hε ψ
      (WeilDeligneRepresentation.classOf
        (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter E).toMonoidHom
          (FiniteRepresentation.restrict
            (weilEquiv F E g : localWeilGroup E →ₜ* localWeilGroup F).toMonoidHom V)))
      (WeilDeligneRepresentation.classOf
        (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter E).toMonoidHom
          (FiniteRepresentation.restrict
            (weilEquiv F E g : localWeilGroup E →ₜ* localWeilGroup F).toMonoidHom W))) c m := by
  rw [isArithmeticPairEpsilonFactor_iff] at h ⊢
  refine ⟨?_, ⟨Correspondence.baseGeometricFrobenius E⟩⟩
  rw [← mapExtension_baseExtension F E g]
  exact isEpsilonFactorAt_transport F E g eE ε hε hε' ψF ψ hψ V W c m h.1

/-- **Arithmetic pair epsilon factors of unitary basis classes along `g`.** -/
theorem isArithmeticPairEpsilonFactor_restrictUnitaryBasisEquiv (eE : ReciprocityFamily E)
    (ε : Assignment.{u₂, uE} E) (hε : IsSystem E eE ε)
    (hε' : IsSystem F (transportFamily F E g eE) (transportAssignment F E g ε))
    (ψF : Correspondence.NontrivialAdditiveCharacter F)
    (ψ : Correspondence.NontrivialAdditiveCharacter E) (hψ : ∀ x : F.Carrier, ψ (g x) = ψF x)
    (a b : LocalWeil.UnitaryBasis.{u₁, uW} F) (c : ℂˣ) (m : ℤ)
    (h : Correspondence.IsArithmeticPairEpsilonFactor F (transportFamily F E g eE)
      (transportAssignment F E g ε) hε' ψF
      (LocalWeil.unitaryBasisPairClass F a) (LocalWeil.unitaryBasisPairClass F b) c m) :
    Correspondence.IsArithmeticPairEpsilonFactor E eE ε hε ψ
      (LocalWeil.unitaryBasisPairClass E (Weil.restrictUnitaryBasisEquiv (weilEquiv F E g) a))
      (LocalWeil.unitaryBasisPairClass E (Weil.restrictUnitaryBasisEquiv (weilEquiv F E g) b))
      c m := by
  obtain ⟨V, hV⟩ := Quotient.exists_rep (Weil.underlyingClass (localWeilGroup F) a.val)
  obtain ⟨W, hW⟩ := Quotient.exists_rep (Weil.underlyingClass (localWeilGroup F) b.val)
  rw [LocalWeil.unitaryBasisPairClass_eq_classOf F a V hV,
    LocalWeil.unitaryBasisPairClass_eq_classOf F b W hW] at h
  rw [LocalWeil.unitaryBasisPairClass_restrictUnitaryBasisEquiv F E (weilEquiv F E g) a V hV,
    LocalWeil.unitaryBasisPairClass_restrictUnitaryBasisEquiv F E (weilEquiv F E g) b W hW]
  exact isArithmeticPairEpsilonFactor_zeroMonodromy_transport F E g eE ε hε hε' ψF ψ hψ V W c m h

/-- **Virtual arithmetic pair epsilon factors along `g`.** Every virtual certificate
`(c, m)` of unitary virtual Weil classes `x ⊗ y` over `F`, for the transported
system and `ψ_F`, is one of the classes restricted along `W_E ≅ W_F`, for `ε` and
the character `ψ` with `ψ ∘ g = ψ_F`. -/
theorem isUnitaryPairEpsilonFactor_transport (eE : ReciprocityFamily E)
    (ε : Assignment.{u₂, uE} E) (hε : IsSystem E eE ε)
    (hε' : IsSystem F (transportFamily F E g eE) (transportAssignment F E g ε))
    (ψF : Correspondence.NontrivialAdditiveCharacter F)
    (ψ : Correspondence.NontrivialAdditiveCharacter E) (hψ : ∀ x : F.Carrier, ψ (g x) = ψF x)
    (x y : LocalWeil.UnitaryLattice.{u₁, uW} F) (c : ℂˣ × ℤ)
    (h : LocalWeil.IsUnitaryPairEpsilonFactor F (transportFamily F E g eE)
      (transportAssignment F E g ε) hε' ψF x y c) :
    LocalWeil.IsUnitaryPairEpsilonFactor E eE ε hε ψ
      (Weil.restrictUnitaryLatticeEquiv (weilEquiv F E g) x)
      (Weil.restrictUnitaryLatticeEquiv (weilEquiv F E g) y) c :=
  LocalWeil.isUnitaryPairEpsilonFactor_restrictUnitaryLatticeEquiv (weilEquiv F E g)
    (fun a b c m hab => isArithmeticPairEpsilonFactor_restrictUnitaryBasisEquiv F E g eE ε hε hε'
      ψF ψ hψ a b c m hab) h

end Langlands.LocalFactor.NonabelianSystem.FieldTransport
