import Langlands.Group.GL.Blocks
import Langlands.Group.GL.Padic
import Langlands.Representation.Category.Basic
import Langlands.Representation.Jacquet.Coinvariants
import Langlands.Representation.Smooth.Admissibility.EquivalenceProof
import Langlands.Representation.Unitary.Basic

/-!
# Actual supercuspidal representations and their isomorphism classes

The vanishing condition concerns the actual Jacquet quotient for every proper
ordered block parabolic and every conjugate of its unipotent radical.
-/

noncomputable section

open CategoryTheory

namespace Langlands

universe uR uG uV uW uF

namespace Jacquet

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module R V]
  {W : Type uW} [AddCommGroup W] [Module R W]
  {ρ : Representation R G V} {σ : Representation R G W}

/-- An actual ambient equivalence induces a linear equivalence of coinvariants. -/
def coinvariantsEquiv (e : ρ.Equiv σ) (N : Subgroup G) :
    Coinvariants ρ N ≃ₗ[R] Coinvariants σ N where
  __ := Representation.Coinvariants.map _ _ (restrictMap e.toIntertwiningMap N)
  invFun := Representation.Coinvariants.map _ _ (restrictMap e.symm.toIntertwiningMap N)
  left_inv x := by
    obtain ⟨v, rfl⟩ := mk_surjective ρ N x
    change mk ρ N (e.symm (e v)) = mk ρ N v
    rw [e.symm_apply_apply]
  right_inv x := by
    obtain ⟨w, rfl⟩ := mk_surjective σ N x
    change mk σ N (e (e.symm w)) = mk σ N w
    rw [e.apply_symm_apply]

@[simp]
theorem coinvariantsEquiv_mk (e : ρ.Equiv σ) (N : Subgroup G) (v : V) :
    coinvariantsEquiv e N (mk ρ N v) = mk σ N (e v) := rfl

/-- Vanishing of the quotient is invariant under an actual representation equivalence. -/
theorem coinvariants_subsingleton_iff (e : ρ.Equiv σ) (N : Subgroup G) :
    Subsingleton (Coinvariants ρ N) ↔ Subsingleton (Coinvariants σ N) := by
  constructor
  · intro h
    let := h
    exact ⟨fun x y => (coinvariantsEquiv e N).symm.injective (Subsingleton.elim _ _)⟩
  · intro h
    let := h
    exact ⟨fun x y => (coinvariantsEquiv e N).injective (Subsingleton.elim _ _)⟩

end Jacquet

namespace GeneralLinear

variable {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ}

/-- The actual conjugate matrix subgroup of a standard block unipotent radical. -/
def BlockShape.conjugateUnipotent (B : BlockShape n) (g : GeneralLinear n F) :
    Subgroup (GeneralLinear n F) :=
  (B.unipotentSubgroup F).map (MulAut.conj g).toMonoidHom

/-- Admissibility and zero actual Jacquet quotients for all proper block
parabolics and their conjugates. Irreducibility is imposed separately on classes. -/
def IsSupercuspidal {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear n F) V) : Prop :=
  IsAdmissible ρ ∧
    ∀ B : BlockShape n, B.parabolic F ≠ ⊤ →
      ∀ g : GeneralLinear n F,
        Subsingleton (Jacquet.Coinvariants ρ (B.conjugateUnipotent g))

theorem isSupercuspidal_of_equiv
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GeneralLinear n F) V}
    {σ : Representation ℂ (GeneralLinear n F) W}
    (e : ρ.Equiv σ) (hρ : IsSupercuspidal ρ) : IsSupercuspidal σ := by
  refine ⟨isAdmissible_of_equiv e hρ.1, ?_⟩
  intro B hB g
  exact (Jacquet.coinvariants_subsingleton_iff e _).mp (hρ.2 B hB g)

theorem isSupercuspidal_iff_of_equiv
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GeneralLinear n F) V}
    {σ : Representation ℂ (GeneralLinear n F) W}
    (e : ρ.Equiv σ) : IsSupercuspidal ρ ↔ IsSupercuspidal σ :=
  ⟨isSupercuspidal_of_equiv e, isSupercuspidal_of_equiv e.symm⟩

/-- The actual irreducible objects satisfying the Jacquet vanishing condition. -/
def supercuspidalProperty :
    ObjectProperty (SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F)) :=
  fun A => A.IsIrreducible ∧ IsSupercuspidal A.representation

/-- A full subcategory of the coherent smooth representation category. -/
abbrev SupercuspidalRep :=
  (supercuspidalProperty (F := F) (n := n)).FullSubcategory

/-- Isomorphism classes at the specified carrier universe, without resizing. -/
def SupercuspidalClass :=
  Quotient (isIsomorphicSetoid (SupercuspidalRep.{uF, uV} (F := F) (n := n)))

/-- The actual underlying irreducible admissible object. -/
def SupercuspidalRep.toIrreducibleAdmissible
    (A : SupercuspidalRep.{uF, uV} (F := F) (n := n)) :
    IrreducibleAdmissibleRep.{0, uF, uV} (k := ℂ) (G := GeneralLinear n F) :=
  ⟨A.obj, A.property.1, A.property.2.1⟩

/-- Forget the supercuspidal condition through the existing full subcategories. -/
def SupercuspidalRep.toIrreducibleAdmissibleFunctor :
    SupercuspidalRep.{uF, uV} (F := F) (n := n) ⥤
      IrreducibleAdmissibleRep.{0, uF, uV} (k := ℂ) (G := GeneralLinear n F) :=
  ObjectProperty.ιOfLE (fun _ h => ⟨h.1, h.2.1⟩)

/-- Send an actual supercuspidal object to its isomorphism class. -/
def SupercuspidalRep.isoClass
    (A : SupercuspidalRep.{uF, uV} (F := F) (n := n)) :
    SupercuspidalClass.{uV, uF} (F := F) (n := n) :=
  Quotient.mk _ A

theorem SupercuspidalRep.isoClass_eq_iff
    (A B : SupercuspidalRep.{uF, uV} (F := F) (n := n)) :
    A.isoClass = B.isoClass ↔ Nonempty (A ≅ B) := Quotient.eq

/-- The genuine map into the full irreducible admissible class space. -/
def SupercuspidalClass.toSmoothDualClass :
    SupercuspidalClass.{uV, uF} (F := F) (n := n) →
      SmoothDualClass.{0, uF, uV} (k := ℂ) (G := GeneralLinear n F) :=
  Quotient.map SupercuspidalRep.toIrreducibleAdmissible (by
    rintro A B ⟨e⟩
    exact ⟨SupercuspidalRep.toIrreducibleAdmissibleFunctor.mapIso e⟩)

/-- No extra identification is introduced by forgetting supercuspidality. -/
theorem SupercuspidalClass.toSmoothDualClass_injective :
    Function.Injective
      (SupercuspidalClass.toSmoothDualClass :
        SupercuspidalClass.{uV, uF} (F := F) (n := n) →
          SmoothDualClass.{0, uF, uV} (k := ℂ) (G := GeneralLinear n F)) := by
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro A B h
  apply Quotient.sound
  obtain ⟨e⟩ := Quotient.exact h
  exact ⟨ObjectProperty.isoMk _
    ((irreducibleAdmissibleProperty (k := ℂ) (G := GeneralLinear n F)).ι.mapIso e)⟩

/-- Unitarizability is an honest property of the supercuspidal isomorphism class. -/
def SupercuspidalClass.IsUnitarizable :
    SupercuspidalClass.{uV, uF} (F := F) (n := n) → Prop :=
  Quotient.lift (fun A => Langlands.IsUnitarizable A.obj.representation) (by
    rintro A B ⟨e⟩
    apply propext
    exact isUnitarizable_iff_of_equiv
      (SmoothRep.equivOfIso ((supercuspidalProperty (F := F) (n := n)).ι.mapIso e)))

/-- Unitary supercuspidal classes are a subset of the genuine supercuspidal class space. -/
def UnitarySupercuspidalClass :=
  {a : SupercuspidalClass.{uV, uF} (F := F) (n := n) //
    SupercuspidalClass.IsUnitarizable a}

end GeneralLinear

namespace PadicField

variable {p : ℕ} [Fact p.Prime]

/-- The genuine supercuspidal class space of any p-adic field in positive rank.
The module carrier universe remains explicit. -/
abbrev SupercuspidalClass (F : PadicField.{uF} p) (n : ℕ) (_hn : 0 < n) :=
  letI := F.canonicalTopologicalData.topology
  GeneralLinear.SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := n)

end PadicField
end Langlands
