import Langlands.Representation.Category.FiniteIndexRestriction
import Langlands.Representation.CompactCoefficient.Subquotients

/-! # Detecting compact irreducible types with fixed vectors -/

noncomputable section

open CategoryTheory

namespace Langlands.CompactCoefficient

universe uG uV uW

section Detection

variable {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

set_option backward.isDefEq.respectTransparency false in
/-- A nonzero vector in a semisimple representation has a nonzero projection
onto an irreducible subrepresentation. -/
theorem exists_irreducible_projection_nonzero
    (ρ : Representation ℂ G V) (hs : ρ.IsSemisimpleRepresentation)
    {v : V} (hv : v ≠ 0) :
    ∃ S : Subrepresentation ρ, S.toRepresentation.IsIrreducible ∧
      ∃ q : ρ.IntertwiningMap S.toRepresentation, q v ≠ 0 := by
  let : IsSemisimpleModule (MonoidAlgebra ℂ G) ρ.asModule :=
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mp hs
  obtain ⟨s, e, -, hsimple⟩ :=
    IsSemisimpleModule.exists_linearEquiv_dfinsupp (MonoidAlgebra ℂ G) ρ.asModule
  obtain ⟨i, hi⟩ : ∃ i : s, e v i ≠ 0 := by
    by_contra! h
    apply hv
    apply e.injective
    ext i
    simpa using h i
  let S : Subrepresentation ρ := Subrepresentation.ofSubmodule' i.val
  have hS : S.toRepresentation.IsIrreducible := by
    apply FiniteIndexRestriction.isIrreducible_toRepresentation_of_isAtom
    exact (Subrepresentation.subrepresentationSubmoduleOrderIso.isAtom_iff S).mp
      (isSimpleModule_iff_isAtom.mp (hsimple i))
  let q : ρ.IntertwiningMap S.toRepresentation :=
    { toLinearMap :=
        { toFun := fun w => ⟨(e w i).val, (e w i).property⟩
          map_add' := fun _ _ => by ext; simp
          map_smul' := fun c w => by
            apply Subtype.ext
            have h := congrArg (fun f => (f i).val)
              ((e.restrictScalars ℂ).map_smul c w)
            exact h }
      isIntertwining' g := by
        ext w
        change (e (ρ g w) i).val = ρ g (e w i).val
        have h := congrArg (fun f => (f i).val)
          (e.map_smul (MonoidAlgebra.of ℂ G g) w)
        simp only [DFinsupp.smul_apply, Submodule.coe_smul,
          MonoidAlgebra.of_apply, Representation.single_smul, one_smul] at h
        exact h }
  refine ⟨S, hS, q, ?_⟩
  intro hq
  apply hi
  apply Subtype.ext
  exact congrArg Subtype.val hq

end Detection

section FixedTypes

variable {G : Type uG} [Group G] [TopologicalSpace G]
  (A : SmoothRep.{0, uG, uV} ℂ G) (K : Subgroup G)

/-- An irreducible compact-coefficient invariant subspace with nonzero fixed
vectors and a nonzero equivariant projection from the ambient representation. -/
structure CompactFixedType where
  space : Subrepresentation A.representation
  irreducible : space.toRepresentation.IsIrreducible
  compact : HasCompactSmoothDualCoefficients space.toRepresentation
  projection : A.representation.IntertwiningMap space.toRepresentation
  projection_ne_zero : projection ≠ 0
  fixed : fixedVectors space.toRepresentation K ≠ ⊥

/-- A semisimple compact-coefficient representation with nonzero fixed space
has a compact irreducible fixed type. -/
theorem nonempty_compactFixedType
    (hs : A.representation.IsSemisimpleRepresentation)
    (hc : HasCompactSmoothDualCoefficients A.representation)
    (hK : fixedVectors A.representation K ≠ ⊥) :
    Nonempty (CompactFixedType A K) := by
  obtain ⟨v, hvK, hv⟩ := (fixedVectors A.representation K).ne_bot_iff.mp hK
  obtain ⟨S, hS, q, hqv⟩ :=
    exists_irreducible_projection_nonzero A.representation hs hv
  have hq : q ≠ 0 := by
    intro h
    exact hqv (by rw [h]; rfl)
  let := hS
  have hsurj : Function.Surjective q :=
    (Representation.IsIrreducible.surjective_or_eq_zero q).resolve_right hq
  refine ⟨⟨S, hS, hc.of_surjective q hsurj, q, hq, ?_⟩⟩
  apply (fixedVectors S.toRepresentation K).ne_bot_iff.mpr
  refine ⟨q v, ?_, hqv⟩
  intro k
  change S.toRepresentation k (q v) = q v
  rw [← q.isIntertwining A.representation S.toRepresentation k v]
  exact congrArg q (hvK k)

/-- Choose the detected compact irreducible fixed type. -/
def detectCompactFixedType
    (hs : A.representation.IsSemisimpleRepresentation)
    (hc : HasCompactSmoothDualCoefficients A.representation)
    (hK : fixedVectors A.representation K ≠ ⊥) :
    CompactFixedType A K :=
  Classical.choice (nonempty_compactFixedType A K hs hc hK)

namespace CompactFixedType

variable {A K}

/-- The detected invariant subspace as an actual compact irreducible smooth object. -/
def compactRep (D : CompactFixedType A K) : IrreducibleCompactCoefficientRep G :=
  ⟨SmoothRep.subrepresentation A D.space, D.irreducible, D.compact⟩

/-- The canonical equivariant inclusion of a detected type. -/
def inclusion (D : CompactFixedType A K) :
    D.space.toRepresentation.IntertwiningMap A.representation where
  toLinearMap := D.space.toSubmodule.subtype
  isIntertwining' _ := LinearMap.ext fun _ => rfl

variable {B : SmoothRep.{0, uG, uW} ℂ G} {L : Subgroup G}

/-- Isomorphic detected types give a nonzero ambient intertwiner. The source
projection is composed with the type isomorphism and the target inclusion. -/
theorem exists_nonzero_intertwiner
    (D : CompactFixedType A K) (E : CompactFixedType B L)
    (e : D.space.toRepresentation.Equiv E.space.toRepresentation) :
    ∃ f : A.representation.IntertwiningMap B.representation, f ≠ 0 := by
  let f := E.inclusion.comp (e.toIntertwiningMap.comp D.projection)
  refine ⟨f, ?_⟩
  intro hf
  apply D.projection_ne_zero
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  change D.projection v = 0
  apply e.injective
  apply Subtype.ext
  have h := congrArg (fun t : A.representation.IntertwiningMap B.representation => t v) hf
  simpa [f, inclusion] using h

end CompactFixedType

end FixedTypes

end Langlands.CompactCoefficient
