import Langlands.Global.Factors.RelativeIsometryFactorStatement
import Langlands.Correspondence.HenniartExtensionDeterminant
import Langlands.Correspondence.HenniartSurjectivityTransfer
import Langlands.Representation.Classification.CuspidalScalarNorm
import Langlands.Representation.Classification.BernsteinOrderZeroPositivity

/-!
# Central characters of unitary virtual supercuspidal classes

Every unitary supercuspidal basis class has exactly one central character, so the
central-character relation `IsUnitaryCentralCharacter` on the unitary lattice is
the graph of the multiplicative extension of the basis central characters. An
irreducible representation with a scalar character `ω` and a witnessed unitary
supercuspidal support `x` has `ω` as central character of `x`.
-/

noncomputable section

universe uF uV

open CategoryTheory

namespace Langlands.VirtualRepresentation.PadicSupercuspidal

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The central character of a unitary supercuspidal basis class: the scalar character
of the corresponding cuspidal datum. -/
def unitaryBasisCentralCharacter (b : UnitaryBasis.{uF, uV} F) : F.Carrierˣ →* ℂˣ :=
  ((unitaryCuspidalDatumBasisEquiv.{uF, uV} F).symm b).val.scalarCharacter

/-- The chosen character is a central character of the basis class. -/
theorem isUnitaryBasisCentralCharacter_unitaryBasisCentralCharacter
    (b : UnitaryBasis.{uF, uV} F) :
    IsUnitaryBasisCentralCharacter F b (unitaryBasisCentralCharacter F b) := by
  obtain ⟨d, rfl⟩ := (unitaryCuspidalDatumBasisEquiv.{uF, uV} F).surjective b
  intro a
  have hd : unitaryBasisCentralCharacter F (unitaryCuspidalDatumBasisEquiv.{uF, uV} F d) =
      d.val.scalarCharacter := by
    simp only [unitaryBasisCentralCharacter, Equiv.symm_apply_apply]
  rw [hd]
  have hrep := d.val.isRepresentedBy_representative
  change Correspondence.SupercuspidalCentralActsBy F (n := ⟨d.val.rank, d.val.rank_pos⟩)
    d.val.cls a (d.val.scalarCharacter a)
  rw [← hrep]
  exact (Henniart.Extension.supercuspidalCentralActsBy_iff F (n := ⟨d.val.rank, d.val.rank_pos⟩)
    d.val.representative a _).mpr (d.val.scalarCharacter_acts a)

/-- The central character of a unitary basis class is unique. -/
theorem IsUnitaryBasisCentralCharacter.eq_unitaryBasisCentralCharacter
    {b : UnitaryBasis.{uF, uV} F} {ω : F.Carrierˣ →* ℂˣ}
    (h : IsUnitaryBasisCentralCharacter F b ω) : ω = unitaryBasisCentralCharacter F b := by
  ext a
  exact congrArg Units.val (Henniart.Extension.supercuspidalCentralActsBy_unique F (h a)
    (isUnitaryBasisCentralCharacter_unitaryBasisCentralCharacter F b a))

/-- The multiplicative extension of the basis central characters. -/
def latticeCentralCharacter (x : UnitaryLattice.{uF, uV} F) : F.Carrierˣ →* ℂˣ :=
  x.prod fun b n => unitaryBasisCentralCharacter F b ^ n

/-- The central-character relation on the unitary lattice is the graph of
`latticeCentralCharacter`. -/
theorem isUnitaryCentralCharacter_iff (x : UnitaryLattice.{uF, uV} F)
    (ω : F.Carrierˣ →* ℂˣ) :
    IsUnitaryCentralCharacter F x ω ↔ ω = latticeCentralCharacter F x := by
  constructor
  · rintro ⟨f, hf, rfl⟩
    apply Finset.prod_congr rfl
    intro b hb
    show f b ^ x b = unitaryBasisCentralCharacter F b ^ x b
    rw [(hf b hb).eq_unitaryBasisCentralCharacter]
  · intro h
    exact ⟨unitaryBasisCentralCharacter F,
      fun b _ => isUnitaryBasisCentralCharacter_unitaryBasisCentralCharacter F b, h⟩

/-- Every unitary virtual class has a central character. -/
theorem isUnitaryCentralCharacter_latticeCentralCharacter (x : UnitaryLattice.{uF, uV} F) :
    IsUnitaryCentralCharacter F x (latticeCentralCharacter F x) :=
  (isUnitaryCentralCharacter_iff F x _).mpr rfl

@[simp]
theorem latticeCentralCharacter_zero :
    latticeCentralCharacter.{uF, uV} F 0 = 1 :=
  Finsupp.prod_zero_index

@[simp]
theorem latticeCentralCharacter_add (x y : UnitaryLattice.{uF, uV} F) :
    latticeCentralCharacter F (x + y) =
      latticeCentralCharacter F x * latticeCentralCharacter F y :=
  Finsupp.prod_add_index' (fun _ => MonoidHom.ext fun a => by simp [MonoidHom.zpow_apply])
    (fun _ _ _ => MonoidHom.ext fun a => by simp [MonoidHom.zpow_apply, zpow_add])

/-- `latticeCentralCharacter` as an additive homomorphism into the character group. -/
private def latticeCentralCharacterHom :
    UnitaryLattice.{uF, uV} F →+ Additive (F.Carrierˣ →* ℂˣ) where
  toFun x := Additive.ofMul (latticeCentralCharacter F x)
  map_zero' := by rw [latticeCentralCharacter_zero]; rfl
  map_add' x y := by rw [latticeCentralCharacter_add]; rfl

@[simp]
theorem latticeCentralCharacter_zsmul (k : ℤ) (x : UnitaryLattice.{uF, uV} F) :
    latticeCentralCharacter F (k • x) = latticeCentralCharacter F x ^ k :=
  by
  have h := map_zsmul (latticeCentralCharacterHom.{uF, uV} F) k x
  calc latticeCentralCharacter F (k • x)
      = Additive.toMul (latticeCentralCharacterHom.{uF, uV} F (k • x)) := rfl
    _ = Additive.toMul (k • latticeCentralCharacterHom.{uF, uV} F x) := by rw [h]
    _ = latticeCentralCharacter F x ^ k := rfl

@[simp]
theorem latticeCentralCharacter_generator (b : UnitaryBasis.{uF, uV} F) :
    latticeCentralCharacter F (generator b) = unitaryBasisCentralCharacter F b := by
  unfold latticeCentralCharacter generator
  rw [Finsupp.prod_single_index (MonoidHom.ext fun a => by simp [MonoidHom.zpow_apply])]
  exact MonoidHom.ext fun a => by simp [MonoidHom.zpow_apply]

/-- On a multiset support, the central character is the product of the scalar
characters of its cuspidal data. -/
theorem latticeCentralCharacter_unitarySupportLattice
    (s : Multiset (PadicField.TopologicalData.UnitaryCuspidalDatum.{uF, uV}
      F.canonicalTopologicalData)) :
    latticeCentralCharacter F (unitarySupportLattice F s) =
      (s.map fun d => d.val.scalarCharacter).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons d s ih =>
    rw [PadicField.TopologicalData.unitarySupportLattice_cons, latticeCentralCharacter_add,
      latticeCentralCharacter_generator, ih, Multiset.map_cons, Multiset.prod_cons]
    simp only [unitaryBasisCentralCharacter, Equiv.symm_apply_apply]

/-- A nonzero carrier has at most one scalar character. -/
private theorem scalar_eq_of_isIrreducible {G : Type*} [Group G] {V : Type*} [AddCommGroup V]
    [Module ℂ V] {ρ : Representation ℂ G V} (hρ : ρ.IsIrreducible) {C : Type*} [Group C]
    {z : C →* G} {ω ω' : C →* ℂˣ}
    (h : ∀ (c : C) (v : V), ρ (z c) v = (ω c : ℂ) • v)
    (h' : ∀ (c : C) (v : V), ρ (z c) v = (ω' c : ℂ) • v) : ω = ω' := by
  obtain ⟨v, hv⟩ : ∃ v : V, v ≠ 0 := by
    by_contra! hzero
    apply (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)
    apply Subrepresentation.toSubmodule_injective
    ext v
    rw [hzero v]
    exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩
  ext c
  exact smul_left_injective ℂ hv ((h c v).symm.trans (h' c v))

/-- If an irreducible representation `π` has the scalar character `ω` and the
unitary supercuspidal support `x`, then `ω` is the central character of `x`. -/
theorem isUnitaryCentralCharacter_of_isUnitaryLatticeSupport {n : ℕ}
    (π : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    {x : UnitaryLattice.{uF, uV} F} (hx : IsUnitaryLatticeSupport F π x)
    (ω : F.Carrierˣ →* ℂˣ)
    (hω : letI := F.canonicalTopologicalData.topology
      ∀ (a : F.Carrierˣ) (f : π), π.representation (GeneralLinear.scalar a) f =
        (ω a : ℂ) • f) :
    IsUnitaryCentralCharacter F x ω := by
  let T := F.canonicalTopologicalData
  let := T.topology
  have := T.generalLinearTopologicalGroup n
  obtain ⟨s, ⟨k, ρ, hρs, h, A, hA, hirr, hsub⟩, rfl⟩ := hx
  rw [isUnitaryCentralCharacter_iff, latticeCentralCharacter_unitarySupportLattice]
  have hblock : ∀ i, Classification.HasScalarCharacter (A i).obj.representation
      GeneralLinear.scalar (ρ i).scalarCharacter := by
    intro i
    obtain ⟨ω', hω'⟩ := SegmentFullJacquet.exists_hasScalarCharacter F T (A i)
    rw [(ρ i).scalarCharacter_eq_of_isRepresentedBy (A i) (hA i) ω' hω']
    exact hω'
  have hind : Classification.HasScalarCharacter
      (T.cuspidalProductInduced ρ h A).representation GeneralLinear.scalar
      (∏ i, (ρ i).scalarCharacter) :=
    T.hasScalarCharacter_normalizedProductInduced (T.cuspidalShape ρ h)
      (σ := fun i => (A i).obj.representation) hblock
  have hπ := hind.of_isSubquotient hsub
  have hprod : (s.map fun d => d.val.scalarCharacter).prod = ∏ i, (ρ i).scalarCharacter := by
    have hmap : (s.map fun d => d.val.scalarCharacter) =
        ((s.map Subtype.val).map fun d => d.scalarCharacter) := by
      rw [Multiset.map_map]
      rfl
    rw [hmap, ← hρs, Multiset.map_coe, Multiset.prod_coe, List.map_ofFn, List.prod_ofFn]
    rfl
  rw [hprod]
  exact scalar_eq_of_isIrreducible hirr hω hπ

end Langlands.VirtualRepresentation.PadicSupercuspidal
