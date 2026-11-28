import Langlands.Algebra.FiniteInvariantModule
import Langlands.Representation.CuspidalSupport.BernsteinComponentWeylBound
import Langlands.Representation.CuspidalSupport.FiniteGroupInvariantFunctions
import Langlands.Representation.CuspidalSupport.StandardLeviInertialFiberBound
import Langlands.Representation.Plancherel.RationalUnramifiedFunctionField

/-! # Uniform module bounds for Bernstein component algebras -/

noncomputable section

namespace Langlands.CuspidalSupport.InvariantFunctions

variable {X : Type*} (R : Subalgebra ℂ (X → ℂ)) {V W : Subgroup (Equiv.Perm X)}

theorem fixedSubalgebra_le (hVW : V ≤ W) :
    fixedSubalgebra R W ≤ fixedSubalgebra R V :=
  fun _ h w hw => h w (hVW hw)

private theorem fixedSubalgebra_eq_fixedPoints_comap (hVW : V ≤ W)
    (hW : ∀ w ∈ W, ∀ f ∈ R, (fun x => f (w x)) ∈ R) :
    letI := action hW
    letI : SMulCommClass W ℂ R := ⟨fun _ _ _ => rfl⟩
    fixedSubalgebra R V = FixedPoints.subalgebra ℂ R (V.comap W.subtype) := by
  let := action hW
  ext f
  change (∀ w ∈ V, ∀ x, (f : X → ℂ) (w x) = (f : X → ℂ) x) ↔
    ∀ w : V.comap W.subtype, w.val • f = f
  constructor
  · intro hf w
    apply Subtype.ext
    funext x
    exact hf _ (V.inv_mem w.property) x
  · intro hf w hw x
    let v : V.comap W.subtype := ⟨⟨w, hVW hw⟩, hw⟩
    have h := congrArg (fun g : R => (g : X → ℂ) x) (hf v⁻¹)
    change (f : X → ℂ) ((w⁻¹)⁻¹ x) = (f : X → ℂ) x at h
    simpa only [inv_inv] using h

private theorem exists_spanningFamily_of_eq {A : Type*} [CommRing A] [Algebra ℂ A]
    {S S' T T' : Subalgebra ℂ A} {n : ℕ}
    (hS : S = S') (hT : T = T') (hST : S ≤ T) (hST' : S' ≤ T')
    (h : letI : Algebra S T := (Subalgebra.inclusion hST).toRingHom.toAlgebra
      ∃ g : Fin n → T, Submodule.span S (Set.range g) = ⊤) :
    letI : Algebra S' T' := (Subalgebra.inclusion hST').toRingHom.toAlgebra
    ∃ g : Fin n → T', Submodule.span S' (Set.range g) = ⊤ := by
  subst S'
  subst T'
  exact h

set_option synthInstance.maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- The uniform bound for fixed points applied to polynomial functions invariant
under nested groups of permutations. -/
theorem exists_spanningFamily_fixedSubalgebra [Nonempty X] [Finite W] (hVW : V ≤ W)
    (hW : ∀ w ∈ W, ∀ f ∈ R, (fun x => f (w x)) ∈ R)
    {d m : ℕ} (hcard : Nat.card W ≤ d)
    (hgen : ∃ s : Finset R, s.card ≤ m ∧ Algebra.adjoin ℂ (s : Set R) = ⊤) :
    letI : Algebra (fixedSubalgebra R W) (fixedSubalgebra R V) :=
      (Subalgebra.inclusion (fixedSubalgebra_le R hVW)).toRingHom.toAlgebra
    ∃ g : Fin (d ^ m) → fixedSubalgebra R V,
      Submodule.span (fixedSubalgebra R W) (Set.range g) = ⊤ := by
  let := action hW
  let : SMulCommClass W ℂ R := ⟨fun _ _ _ => rfl⟩
  let H := V.comap W.subtype
  have hS : fixedSubalgebra R W = FixedPoints.subalgebra ℂ R W := by
    ext f
    change (∀ w ∈ W, ∀ x, (f : X → ℂ) (w x) = (f : X → ℂ) x) ↔
      ∀ w : W, w • f = f
    constructor
    · intro hf w
      apply Subtype.ext
      funext x
      exact hf _ (w⁻¹).property x
    · intro hf w hw x
      have h := congrArg (fun g : R => (g : X → ℂ) x) (hf (⟨w, hw⟩⁻¹))
      exact h
  have hT : fixedSubalgebra R V = FixedPoints.subalgebra ℂ R H :=
    fixedSubalgebra_eq_fixedPoints_comap R hVW hW
  have hST : FixedPoints.subalgebra ℂ R W ≤ FixedPoints.subalgebra ℂ R H :=
    fun _ hf w => hf w.val
  have hbound := exists_spanningFamily_fixedPoints (k := ℂ) (A := R) H d m
  exact exists_spanningFamily_of_eq hS.symm hT.symm hST
    (fixedSubalgebra_le R hVW) (hbound hcard hgen)

end Langlands.CuspidalSupport.InvariantFunctions

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme Langlands.Plancherel
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local notation "j" => fun I => Standard.leviHom i ν (rootSet i ν I)
local notation "H" => bernsteinLeviScheme i ν

local instance invariantBoundAmbientAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance invariantBoundAmbientTopology : TopologicalSpace (rationalPoints G) := pointTopology
local instance invariantBoundLeviClosed (I : Finset (SimpleRoot i ν)) : IsClosedImmersion (j I).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)
local instance invariantBoundLeviAffine (I : Finset (SimpleRoot i ν)) : IsAffine (H I).X.left :=
  isAffine_of_isAffineHom (j I).hom.hom.left
local instance invariantBoundLeviFiniteType (I : Finset (SimpleRoot i ν)) : LocallyOfFiniteType (H I).X.hom := by
  rw [← (j I).hom.hom.w]
  infer_instance
local instance invariantBoundLeviTopology (I : Finset (SimpleRoot i ν)) : TopologicalSpace (rationalPoints (H I)) :=
  rationalPointTopology F (H I).X

private abbrev regular (I : Finset (SimpleRoot i ν)) :=
  unramifiedRegularFunctions (fun ψ => (rationalNormCharacters (H I) ψ).toMul)

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

set_option synthInstance.maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- A common bound for the number of module generators on all ambient components, for
the inclusion from the ambient component invariants to any subgroup's invariants. -/
def BernsteinInvariantModuleBoundStatement : Prop :=
  ∃ B : ℕ, ∀ a : BernsteinCuspidalDatum.{uF, uV} i ν family,
    let R := regular i ν a.roots
    let W := ComponentWeyl.weylGroup (j a.roots) a.representation
    ∀ (V : Subgroup (Equiv.Perm (ComponentWeyl.UChar (H a.roots)))) (hVW : V ≤ W),
      letI : Algebra (InvariantFunctions.fixedSubalgebra R W)
          (InvariantFunctions.fixedSubalgebra R V) :=
        (Subalgebra.inclusion (InvariantFunctions.fixedSubalgebra_le R hVW)).toRingHom.toAlgebra
      ∃ g : Fin B → InvariantFunctions.fixedSubalgebra R V,
        Submodule.span (InvariantFunctions.fixedSubalgebra R W) (Set.range g) = ⊤

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency.types false in
theorem bernsteinInvariantModuleBound :
    BernsteinInvariantModuleBoundStatement.{uF, uV} i ν family := by
  classical
  let := family.finiteSimpleRoots
  let := Fintype.ofFinite (SimpleRoot i ν)
  have hH (I : Finset (SimpleRoot i ν)) : IsConnectedReductive (H I) :=
    (standardLeviSplitComponentStatement F G family.connectedReductive T i family.maximalSplitTorus
      ν family.genericCocharacter (rootSet i ν I) (rootSet_subset i ν I)).1
  have hgen (I : Finset (SimpleRoot i ν)) :
      ∃ s : Finset (regular i ν I), Algebra.adjoin ℂ (s : Set (regular i ν I)) = ⊤ :=
    (rationalUnramifiedRegularFunctions_finiteType (H I)
      (continuous_rationalValuationImageProjection _) (hH I)).out
  choose s hs using hgen
  have hnorm (I) := standardLevi_exists_finite_normalizer_representatives i ν
    family.connectedReductive family.maximalSplitTorus family.genericCocharacter I
  choose n w hw using hnorm
  let C (I : Finset (SimpleRoot i ν)) :=
    centralTrivialUnramifiedCharacters (fun ψ => (rationalNormCharacters (H I) ψ).toMul)
      (Subgroup.center (rationalPoints (H I)))
  let d := Finset.univ.sup fun I => n I * Nat.card (C I)
  let m := Finset.univ.sup fun I => (s I).card
  refine ⟨d ^ m, fun a V hVW => ?_⟩
  have hj : Mono (j a.roots).hom.hom := Over.mono_of_mono_left _
  obtain ⟨hfin, hcard⟩ := ComponentWeyl.rationalWeylGroup_card_le (j a.roots) (w a.roots)
    (hH a.roots) hj (hw a.roots) a.representation a.irreducible
  let := hfin
  have hd : Nat.card (ComponentWeyl.weylGroup (j a.roots) a.representation) ≤ d :=
    hcard.trans (Finset.le_sup (f := fun I => n I * Nat.card (C I)) (Finset.mem_univ a.roots))
  have hm : (s a.roots).card ≤ m :=
    Finset.le_sup (f := fun I => (s I).card) (Finset.mem_univ a.roots)
  exact InvariantFunctions.exists_spanningFamily_fixedSubalgebra (regular i ν a.roots) hVW
    (fun _ hw' _ hf => ComponentWeyl.weylGroup_comp_mem_regular (j a.roots) a.representation hw' hf)
    hd ⟨s a.roots, hm, hs a.roots⟩

end Langlands.CuspidalSupport
