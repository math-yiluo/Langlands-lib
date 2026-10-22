import Langlands.Representation.Classification.SupercuspidalSupport
import Langlands.Representation.Category.ConstituentDichotomyStatement
import Mathlib.RepresentationTheory.Irreducible

/-!
# Proof of the irreducible subquotient dichotomy

An irreducible actual subquotient of a smooth representation `A` is an actual
subquotient of a given invariant subrepresentation `S` or of the actual quotient
`A/S`. The proof takes the inverse image of `S` in an occurrence of the
subquotient, together with the corresponding quotient. Two corollaries give the
kernel/image and image/cokernel alternatives for an intertwiner.
-/

noncomputable section

open CategoryTheory

namespace Langlands.SmoothRep

universe uR uG uV

variable {R : Type uR} [Field R] {G : Type uG} [Group G] [TopologicalSpace G]

/-- An intertwiner vanishing on an invariant submodule descends to the actual
quotient by it. -/
private def quotientLift {A B : SmoothRep.{uR, uG, uV} R G}
    (S : Subrepresentation A.representation) (f : A ⟶ B)
    (h : S.toSubmodule ≤ (hom f).toLinearMap.ker) : quotient A S ⟶ B :=
  ofHom {
    toLinearMap := S.toSubmodule.liftQ (hom f).toLinearMap h
    isIntertwining' g := by
      apply Submodule.linearMap_qext
      ext v
      exact Representation.IntertwiningMap.isIntertwining _ _ (hom f) g v }

/-- A simple actual subquotient of a smooth representation occurs either in an
invariant subrepresentation or in the corresponding quotient. -/
theorem irreducibleSubquotient_dichotomy
    {A D : SmoothRep.{uR, uG, uV} R G} (hD : D.IsIrreducible)
    (h : IsSubquotient D A) (S : Subrepresentation A.representation) :
    IsSubquotient D (subrepresentation A S) ∨ IsSubquotient D (quotient A S) := by
  let : D.representation.IsIrreducible := hD
  obtain ⟨C, i, q, hi, hq⟩ := isSubquotient_iff_exists.mp h
  let f : C ⟶ quotient A S := i ≫ mkQ A S
  let K := (hom f).ker
  let E := subrepresentation C K
  let qK : E ⟶ D := subtype C K ≫ q
  rcases Representation.IsIrreducible.surjective_or_eq_zero (hom qK) with hs | hz
  · left
    let j : E ⟶ subrepresentation A S := ofHom {
      toLinearMap := ((hom i).toLinearMap.comp K.toSubmodule.subtype).codRestrict
        S.toSubmodule (by
          intro x
          have hx := x.property
          change (hom (mkQ A S)) (hom i x.val) = 0 at hx
          exact (Submodule.Quotient.mk_eq_zero S.toSubmodule).mp hx)
      isIntertwining' g := by
        ext x
        exact Subtype.ext (Representation.IntertwiningMap.isIntertwining _ _ (hom i) g x.val) }
    apply isSubquotient_iff_exists.mpr
    refine ⟨E, j, qK, ?_, hs⟩
    intro x y hxy
    apply Subtype.ext
    exact hi (congrArg Subtype.val hxy)
  · right
    have hK : K.toSubmodule ≤ (hom q).toLinearMap.ker := by
      intro x hx
      have hz' := congrArg (fun t : E.representation.IntertwiningMap D.representation => t ⟨x, hx⟩) hz
      exact hz'
    let q' : quotient C K ⟶ D := quotientLift K q hK
    let j : quotient C K ⟶ quotient A S := quotientLift K f le_rfl
    apply isSubquotient_iff_exists.mpr
    refine ⟨quotient C K, j, q', ?_, ?_⟩
    · change Function.Injective (K.toSubmodule.liftQ (hom f).toLinearMap le_rfl)
      apply LinearMap.ker_eq_bot.mp
      exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl
    · intro d
      obtain ⟨c, hc⟩ := hq d
      exact ⟨hom (mkQ C K) c, hc⟩

/-- The actual quotient by an intertwiner's kernel is isomorphic to its image. -/
private def quotientKernelIsoImage {A B : SmoothRep.{uR, uG, uV} R G}
    (f : A ⟶ B) : quotient A (hom f).ker ≅ image f :=
  mkIso <| Representation.Equiv.mk (hom f).toLinearMap.quotKerEquivRange fun g => by
    apply Submodule.linearMap_qext
    ext v
    exact Subtype.ext (Representation.IntertwiningMap.isIntertwining _ _ (hom f) g v)

/-- The kernel/image occurrence alternative for any intertwiner. -/
theorem irreducibleSubquotient_kernel_or_image
    {A B D : SmoothRep.{uR, uG, uV} R G} (hD : D.IsIrreducible)
    (h : IsSubquotient D A) (f : A ⟶ B) :
    IsSubquotient D (kernel f) ∨ IsSubquotient D (image f) := by
  rcases irreducibleSubquotient_dichotomy hD h (hom f).ker with hk | hq
  · exact Or.inl hk
  · exact Or.inr (hq.of_iso_right (quotientKernelIsoImage f))

/-- The image/cokernel occurrence alternative for any intertwiner. -/
theorem irreducibleSubquotient_image_or_cokernel
    {A B D : SmoothRep.{uR, uG, uV} R G} (hD : D.IsIrreducible)
    (h : IsSubquotient D B) (f : A ⟶ B) :
    IsSubquotient D (image f) ∨ IsSubquotient D (cokernel f) :=
  irreducibleSubquotient_dichotomy hD h (hom f).range

/-- The exact published irreducible-subquotient dichotomy. -/
theorem irreducibleSubquotientDichotomy :
    IrreducibleSubquotientDichotomy.{uR, uG, uV} := by
  intro R _ G _ _ A D S hD h
  exact irreducibleSubquotient_dichotomy hD h S

end Langlands.SmoothRep
