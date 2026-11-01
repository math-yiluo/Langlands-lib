import Langlands.Representation.Filtration.ExactSmoothSubquotients
import Langlands.Representation.Filtration.SubquotientAlgebraProof
import Langlands.Representation.Smooth.ConstituentSupport
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Irreducibility detected by an exact smooth functor

A finite-length smooth representation is irreducible if its image is
irreducible and the functor does not kill any of its irreducible subquotients.
The functor and all the hypotheses are explicit; no particular derivative
formula or nonvanishing assertion is supplied here.
-/

noncomputable section
open CategoryTheory

namespace Langlands.ExactFunctorIrreducibility

universe uG uH uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {H : Type uH} [Group H] [TopologicalSpace H]
  (J : SmoothRep.{0,uG,uV} ℂ G ⥤ SmoothRep.{0,uH,uV} ℂ H)

/-- The actual images of all irreducible actual subquotients of `A` are nonzero. -/
def NonvanishingOnIrreducibleSubquotients
    (A : SmoothRep.{0,uG,uV} ℂ G) : Prop :=
  ∀ D : SmoothRep.{0,uG,uV} ℂ G, D.IsIrreducible →
    SmoothRep.IsSubquotient D A → Nontrivial (J.obj D)

variable (hJ : Derivative.Mirabolic.MapsShortExactIntertwiners J)

/-- The nonvanishing condition passes to an actual subquotient. -/
theorem NonvanishingOnIrreducibleSubquotients.of_isSubquotient
    {A B : SmoothRep.{0,uG,uV} ℂ G}
    (h : NonvanishingOnIrreducibleSubquotients J A)
    (hBA : SmoothRep.IsSubquotient B A) :
    NonvanishingOnIrreducibleSubquotients J B :=
  fun D hD hDB => h D hD (smoothSubquotientTransitivity ℂ G A B D hDB hBA)

include hJ in
/-- Short-exactness alone forces the image of a zero carrier to be zero. -/
theorem obj_subsingleton (A : SmoothRep.{0,uG,uV} ℂ G) [Subsingleton A] :
    Subsingleton (J.obj A) := by
  have hex : LinearMap.range (SmoothRep.hom (𝟙 A)).toLinearMap =
      LinearMap.ker (SmoothRep.hom (𝟙 A)).toLinearMap := by
    ext a
    change (∃ b : A, b = a) ↔ a = 0
    exact ⟨fun _ => Subsingleton.elim _ _, fun _ => ⟨a, rfl⟩⟩
  have h := (hJ A A A (𝟙 A) (𝟙 A)
    (fun _ _ h => h) (fun a => ⟨a, rfl⟩) hex).2.1
  rw [J.map_id] at h
  have hz (a : J.obj A) : a = 0 := by
    have ha : a ∈ LinearMap.range (SmoothRep.hom (𝟙 (J.obj A))).toLinearMap :=
      ⟨a, rfl⟩
    rw [h] at ha
    exact ha
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

include hJ in
/-- On a finite-length object whose simple subquotients survive, a zero image
forces the original carrier to be zero. -/
theorem subsingleton_of_obj_subsingleton (A : SmoothRep.{0,uG,uV} ℂ G)
    (hA : A.HasFiniteLength)
    (hdet : NonvanishingOnIrreducibleSubquotients J A)
    [Subsingleton (J.obj A)] : Subsingleton A := by
  classical
  by_cases hz : Subsingleton A
  · exact hz
  · let : Nontrivial A := not_subsingleton_iff_nontrivial.mp hz
    obtain ⟨D, hD, hDA⟩ := SmoothRep.exists_irreducible_subquotient A hA
    obtain ⟨X, i, q, hi, hq⟩ := SmoothRep.isSubquotient_iff_exists.mp
      (ExactSmoothTransport.map_isSubquotient J hJ hDA)
    have hX : Subsingleton X := ⟨fun x y => hi (Subsingleton.elim _ _)⟩
    have hJD : Subsingleton (J.obj D) := by
      constructor
      intro a b
      obtain ⟨x, rfl⟩ := hq a
      obtain ⟨y, rfl⟩ := hq b
      exact congrArg (SmoothRep.hom q) (hX.elim x y)
    exact False.elim ((not_nontrivial_iff_subsingleton.mpr hJD) (hdet D hD hDA))

include hJ in
/-- An irreducible image detects irreducibility when all simple actual
subquotients of the finite-length source survive. -/
theorem isIrreducible_of_obj (A : SmoothRep.{0,uG,uV} ℂ G)
    (hA : A.HasFiniteLength)
    (hdet : NonvanishingOnIrreducibleSubquotients J A)
    (himage : (J.obj A).IsIrreducible) : A.IsIrreducible := by
  classical
  let : (J.obj A).IsIrreducible := himage
  have hJne : Nontrivial (J.obj A) :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ H) (J.obj A).representation.asModule
  have hne : (⊥ : Subrepresentation A.representation) ≠ ⊤ := by
    intro h
    have : Subsingleton A := ⟨fun a b => by
      have hz (v : A) : v = 0 := by
        have hv : v ∈ (⊥ : Subrepresentation A.representation) := by
          rw [h]
          trivial
        exact hv
      exact (hz a).trans (hz b).symm⟩
    exact (not_nontrivial_iff_subsingleton.mpr (obj_subsingleton J hJ A)) hJne
  refine { exists_pair_ne := ⟨⊥, ⊤, hne⟩, eq_bot_or_eq_top := ?_ }
  intro S
  let K := A.subrepresentation S
  let Q := A.quotient S
  have hKA : SmoothRep.IsSubquotient K A :=
    (A.subrepresentation_isSubrepresentation S).isSubquotient
  have hQA : SmoothRep.IsSubquotient Q A :=
    (A.quotient_isQuotient S).isSubquotient
  have hK : K.HasFiniteLength := SmoothRep.hasFiniteLength_of_isSubquotient hA hKA
  have hQ : Q.HasFiniteLength := SmoothRep.hasFiniteLength_of_isSubquotient hA hQA
  have he := hJ K A Q (A.subtype S) (A.mkQ S)
    (A.subtype_injective S) (A.mkQ_surjective S)
    (by
      change LinearMap.range S.toSubmodule.subtype = LinearMap.ker S.toSubmodule.mkQ
      rw [Submodule.range_subtype, Submodule.ker_mkQ])
  by_cases hz : Subsingleton (J.obj K)
  · left
    let := hz
    have hzero := subsingleton_of_obj_subsingleton J hJ K hK
      (hdet.of_isSubquotient J hKA)
    apply le_antisymm _ bot_le
    intro a ha
    change a = 0
    exact congrArg Subtype.val (hzero.elim (⟨a, ha⟩ : K) 0)
  · right
    have hi0 : SmoothRep.hom (J.map (A.subtype S)) ≠ 0 := by
      intro hi
      apply hz
      exact ⟨fun a b => he.1 (by simp [hi])⟩
    have hi := (Representation.IsIrreducible.surjective_or_eq_zero
      (SmoothRep.hom (J.map (A.subtype S)))).resolve_right hi0
    have hq0 (a : J.obj A) : SmoothRep.hom (J.map (A.mkQ S)) a = 0 := by
      have ha : a ∈ LinearMap.range
          (SmoothRep.hom (J.map (A.subtype S))).toLinearMap := hi a
      rw [he.2.1] at ha
      exact ha
    have : Subsingleton (J.obj Q) := ⟨fun a b => by
      obtain ⟨a, rfl⟩ := he.2.2 a
      obtain ⟨b, rfl⟩ := he.2.2 b
      rw [hq0 a, hq0 b]⟩
    have hzero := subsingleton_of_obj_subsingleton J hJ Q hQ
      (hdet.of_isSubquotient J hQA)
    apply le_antisymm le_top
    intro a _
    exact (Submodule.Quotient.mk_eq_zero S.toSubmodule).mp
      (hzero.elim (SmoothRep.hom (A.mkQ S) a) 0)

/-- Every representation with a one-dimensional carrier is irreducible,
independently of the acting group. -/
theorem isIrreducible_of_finrank_eq_one (A : SmoothRep.{0,uH,uV} ℂ H)
    (hA : Module.finrank ℂ A = 1) : A.IsIrreducible := by
  have : IsSimpleOrder (Submodule ℂ A) :=
    is_simple_module_of_finrank_eq_one (K := ℂ) hA
  refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
  · intro h
    exact bot_ne_top (congrArg Subrepresentation.toSubmodule h)
  · intro S
    rcases eq_bot_or_eq_top S.toSubmodule with h | h
    · exact Or.inl (Subrepresentation.toSubmodule_injective h)
    · exact Or.inr (Subrepresentation.toSubmodule_injective h)

include hJ in
/-- The one-dimensional-image version of the exact-functor criterion. -/
theorem isIrreducible_of_finrank_obj_eq_one (A : SmoothRep.{0,uG,uV} ℂ G)
    (hA : A.HasFiniteLength)
    (hdet : NonvanishingOnIrreducibleSubquotients J A)
    (hdim : Module.finrank ℂ (J.obj A) = 1) : A.IsIrreducible :=
  isIrreducible_of_obj J hJ A hA hdet (isIrreducible_of_finrank_eq_one (J.obj A) hdim)

end Langlands.ExactFunctorIrreducibility
