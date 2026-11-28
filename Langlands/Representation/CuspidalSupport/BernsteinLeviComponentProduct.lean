import Langlands.Algebra.UniformProductModule
import Langlands.Representation.CuspidalSupport.BernsteinCenterComponentProduct
import Langlands.Representation.CuspidalSupport.BernsteinInvariantModuleBound

/-! # The finite map of Bernstein component products for a standard Levi -/

noncomputable section

set_option maxHeartbeats 250000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

open BernsteinCuspidalDatum
open ComponentWeyl (UChar invariantAlgebra weylGroup)

private abbrev commRingHom (R S : Type*) [CommRing R] [CommRing S] : Type _ :=
  R →+* S

private def componentwiseHom {I J : Type*} (R : I → Type*) (S : J → Type*)
    [∀ i, CommRing (R i)] [∀ j, CommRing (S j)]
    (p : J → I) (h : ∀ j, R (p j) →+* S j) : commRingHom (∀ i, R i) (∀ j, S j) where
  toFun f j := h j (f (p j))
  map_one' := funext fun j => (h j).map_one
  map_mul' f g := funext fun j => (h j).map_mul (f (p j)) (g (p j))
  map_zero' := funext fun j => (h j).map_zero
  map_add' f g := funext fun j => (h j).map_add (f (p j)) (g (p j))

private theorem componentwiseHom_finite {I J : Type*}
    (R : I → Type*) (S : J → Type*) [∀ i, CommRing (R i)] [∀ j, CommRing (S j)]
    (p : J → I) (h : ∀ j, R (p j) →+* S j)
    (hf : ∃ L : ℕ, ∀ i, Nonempty ({j // p j = i} ↪ Fin L))
    (hg : ∃ K : ℕ, ∀ j, letI := (h j).toAlgebra
      ∃ g : Fin K → S j, Submodule.span (R (p j)) (Set.range g) = ⊤) :
    (componentwiseHom R S p h).Finite := by
  obtain ⟨L, hL⟩ := hf
  obtain ⟨K, hK⟩ := hg
  let instAlgebra (j : J) : Algebra (R (p j)) (S j) := (h j).toAlgebra
  let := (componentwiseHom R S p h).toAlgebra
  obtain ⟨g, hspan⟩ := exists_spanningFamily_pi_of_boundedFibers R S p (fun _ _ _ => rfl) hL hK
  exact ⟨hspan ▸ Submodule.fg_span (Set.finite_range g)⟩

private theorem spanningFamily_comp_equiv {A B C E K : Type*} [CommRing A] [CommRing B]
    [CommRing C] [CommRing E] [Fintype K] (e : A ≃+* B) (inc : B →+* C) (d : C ≃+* E)
    (h : letI := inc.toAlgebra
      ∃ g : K → C, Submodule.span B (Set.range g) = ⊤) :
    letI := (d.toRingHom.comp (inc.comp e.toRingHom)).toAlgebra
    ∃ g : K → E, Submodule.span A (Set.range g) = ⊤ := by
  let := inc.toAlgebra
  let := (d.toRingHom.comp (inc.comp e.toRingHom)).toAlgebra
  obtain ⟨g, hg⟩ := h
  refine ⟨fun k => d (g k), Submodule.eq_top_iff'.mpr fun x => ?_⟩
  have hx : d.symm x ∈ Submodule.span B (Set.range g) := by rw [hg]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun B).mp hx
  refine (Submodule.mem_span_range_iff_exists_fun A).mpr ⟨fun k => e.symm (c k), ?_⟩
  calc
    _ = ∑ k, d (inc (c k) * g k) := by
      apply Finset.sum_congr rfl
      intro k _
      change d (inc (e (e.symm (c k)))) * d (g k) = d (inc (c k) * g k)
      rw [e.apply_symm_apply, d.map_mul]
    _ = d (∑ k, c k • g k) := (map_sum d _ _).symm
    _ = x := (congrArg d hc).trans (d.apply_symm_apply x)

namespace BernsteinLeviPresentation

universe u v

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {G M : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffineHom M.X.hom]
  [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType M.X.hom]

attribute [local instance] ambientAffine canonicalTopology standardLeviClosed standardLeviAffine
  BernsteinLeviPresentation.standardLeviFiniteType

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  [LocallyCompactSpace (rationalPoints M)] [NonarchimedeanGroup (rationalPoints M)]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}
  {J : Finset (SimpleRoot i ν)} {j : M ⟶ G}
  (D : BernsteinLeviPresentation i ν J j) (family : BernsteinStandardFamily i ν)

private abbrev intrinsicDatum (s : BernsteinInertialClass.{u, v} D.torus ν (D.standardFamily family)) :=
  bernsteinComponentDatum D.torus ν (D.standardFamily family) s

private abbrev ambientDatumAt (s : BernsteinInertialClass.{u, v} D.torus ν (D.standardFamily family)) :=
  (D.ambientDatum family (intrinsicDatum D family s)).val

private abbrev ambientClassAt (s : BernsteinInertialClass.{u, v} D.torus ν (D.standardFamily family)) :=
  bernsteinInertialClass i ν family (ambientDatumAt D family s)

private abbrev ambientRepresentative
    (s : BernsteinInertialClass.{u, v} D.torus ν (D.standardFamily family)) :=
  bernsteinComponentDatum i ν family (ambientClassAt D family s)

private abbrev ambientComponent (t : BernsteinInertialClass.{u, v} i ν family) : Type _ :=
  (bernsteinComponentDatum i ν family t).componentAlgebra

private abbrev intrinsicComponent
    (s : BernsteinInertialClass.{u, v} D.torus ν (D.standardFamily family)) : Type _ :=
  (intrinsicDatum D family s).componentAlgebra

private theorem ambientClassAt_eq (s : BernsteinInertialClass.{u, v} D.torus ν (D.standardFamily family)) :
    ambientClassAt D family s =
      standardLeviInertialToAmbient i ν family J (D.inertialClassEmbedding family s) := by
  conv_rhs => rw [← bernsteinComponentDatum_class D.torus ν (D.standardFamily family) s]
  rw [D.inertialClassEmbedding_class, standardLeviInertialToAmbient_class]

private theorem ambientDatumAt_related
    (s : BernsteinInertialClass.{u, v} D.torus ν (D.standardFamily family)) :
    IsBernsteinInertiaRelated i ν family
      (bernsteinComponentDatum i ν family (ambientClassAt D family s)) (ambientDatumAt D family s) :=
  (bernsteinInertialClass_eq_iff i ν family _ _).mp
    (bernsteinComponentDatum_class i ν family (ambientClassAt D family s))

private abbrev relativeLeviAt
    (a : BernsteinCuspidalDatum.{u, v} D.torus ν (D.standardFamily family)) :
    bernsteinLeviScheme i ν (D.ambientDatum family a).val.roots ⟶ M :=
  D.relativeLeviHom family a.roots

private abbrev relativeAlgebra
    (a : BernsteinCuspidalDatum.{u, v} D.torus ν (D.standardFamily family)) :=
  invariantAlgebra (relativeLeviAt D family a) (D.ambientDatum family a).val.representation

omit [LocallyOfFiniteType M.X.hom] in
private theorem relativeWeyl_le_at
    (a : BernsteinCuspidalDatum.{u, v} D.torus ν (D.standardFamily family)) :
    let b := (D.ambientDatum family a).val
    weylGroup (relativeLeviAt D family a) b.representation ≤
      weylGroup (Standard.leviHom i ν (rootSet i ν b.roots)) b.representation :=
  D.relativeWeyl_le family a

private def invariantInclusion {X : Type*} (R : Subalgebra ℂ (X → ℂ))
    {V W : Subgroup (Equiv.Perm X)} (h : V ≤ W) :
    InvariantFunctions.fixedSubalgebra R W →+* InvariantFunctions.fixedSubalgebra R V :=
  (Subalgebra.inclusion (InvariantFunctions.fixedSubalgebra_le R h)).toRingHom

variable (b : BernsteinCuspidalDatum.{u, v} i ν family)
  (q : bernsteinLeviScheme i ν b.roots ⟶ M)
  (h : weylGroup q b.representation ≤
    weylGroup (Standard.leviHom i ν (rootSet i ν b.roots)) b.representation)

private abbrev datumRegular := unramifiedRegularFunctions (fun ψ =>
  (rationalNormCharacters (bernsteinLeviScheme i ν b.roots) ψ).toMul)

private def inclusionInferred := invariantInclusion (datumRegular family b) h

private def inclusionAtDatum : b.componentAlgebra →+* invariantAlgebra q b.representation := by
  with_reducible exact inclusionInferred family b q h

private def relativeInclusion (a : BernsteinCuspidalDatum.{u, v} D.torus ν (D.standardFamily family)) :
    (D.ambientDatum family a).val.componentAlgebra →+* relativeAlgebra D family a := by
  with_reducible
    exact inclusionAtDatum family (D.ambientDatum family a).val
      (relativeLeviAt D family a) (relativeWeyl_le_at D family a)

set_option allowUnsafeReducibility true in
attribute [local reducible] BernsteinLeviPresentation.ambientDatum in
private def relativeTransport (a : BernsteinCuspidalDatum.{u, v} D.torus ν (D.standardFamily family)) :
    a.componentAlgebra ≃ₐ[ℂ] relativeAlgebra D family a := by
  with_reducible exact D.relativeComponentEquiv family a

private def componentToAmbientDatum
    (s : BernsteinInertialClass.{u, v} D.torus ν (D.standardFamily family)) :
    (ambientRepresentative D family s).componentAlgebra ≃+*
      (ambientDatumAt D family s).componentAlgebra :=
  componentEquiv (a := ambientRepresentative D family s) (b := ambientDatumAt D family s)
    (ambientDatumAt_related D family s)

private def componentHom (s : BernsteinInertialClass.{u, v} D.torus ν (D.standardFamily family)) :
    ambientComponent family (ambientClassAt D family s) →+* intrinsicComponent D family s := by
  with_reducible
    exact (relativeTransport D family (intrinsicDatum D family s)).symm.toRingEquiv.toRingHom.comp
      ((relativeInclusion D family (intrinsicDatum D family s)).comp
        (componentToAmbientDatum D family s).toRingHom)

/-- Restrict ambient component functions to the components of the represented standard Levi. -/
def componentProductHom : commRingHom (BernsteinComponentProduct.{u, v} i ν family)
    (BernsteinComponentProduct.{u, v} D.torus ν (D.standardFamily family)) := by
  with_reducible
    exact componentwiseHom (ambientComponent.{u, v} family) (intrinsicComponent.{u, v} D family)
      (ambientClassAt.{u, v} D family) (componentHom.{u, v} D family)

private abbrev ambientParameterAt
    (a : BernsteinCuspidalDatum.{u, v} D.torus ν (D.standardFamily family))
    (χ : a.unramifiedParameter) : UChar (bernsteinLeviScheme i ν (D.ambientDatum family a).val.roots) :=
  rationalUnramifiedCharacterTransport (D.innerLeviIso family a.roots) χ

private theorem inverse_transport_eval {R S : Type*} [Semiring R] [Semiring S]
    [Algebra ℂ R] [Algebra ℂ S] (e : R ≃ₐ[ℂ] S) (f : R → ℂ) (g : S → ℂ)
    (h : ∀ r, g (e r) = f r) (y : S) : f (e.symm y) = g y :=
  (h (e.symm y)).symm.trans (congrArg g (e.apply_symm_apply y))

set_option allowUnsafeReducibility true in
attribute [local reducible] BernsteinLeviPresentation.ambientDatum relativeTransport in
private theorem relativeRestriction_eval
    (a : BernsteinCuspidalDatum.{u, v} D.torus ν (D.standardFamily family))
    (x : (D.ambientDatum family a).val.componentAlgebra) (χ : a.unramifiedParameter) :
    ((relativeTransport D family a).symm (relativeInclusion D family a x)).val.val χ =
      x.val.val (ambientParameterAt D family a χ) := by
  let e := relativeTransport D family a
  let ω := ambientParameterAt D family a χ
  let f (g : a.componentAlgebra) : ℂ := g.val.val χ
  let g (g : relativeAlgebra D family a) : ℂ := g.val.val ω
  have h (z : a.componentAlgebra) : g (e z) = f z := by
    with_reducible exact D.relativeComponentEquiv_eval family a z χ
  exact inverse_transport_eval e f g h (relativeInclusion D family a x)

private def ambientCoordinateChange
    (s : BernsteinInertialClass.{u, v} D.torus ν (D.standardFamily family))
    (x : ambientComponent family (ambientClassAt D family s)) : (ambientDatumAt D family s).componentAlgebra := by
  with_reducible exact (componentToAmbientDatum D family s).toFun x

private theorem componentProductHom_at
    (f : BernsteinComponentProduct.{u, v} i ν family)
    (s : BernsteinInertialClass.{u, v} D.torus ν (D.standardFamily family))
    (χ : (intrinsicDatum D family s).unramifiedParameter) :
    (D.componentProductHom.{u, v} family f s).val.val χ =
      (ambientCoordinateChange D family s (f (ambientClassAt D family s))).val.val
        (ambientParameterAt D family (intrinsicDatum D family s) χ) := by
  unfold componentProductHom componentwiseHom componentHom ambientCoordinateChange
  exact relativeRestriction_eval D family (intrinsicDatum D family s) _ χ

private theorem componentEquiv_eval_productOn
    (f : BernsteinComponentProduct.{u, v} i ν family)
    (t : BernsteinInertialClass.{u, v} i ν family)
    (a : BernsteinCuspidalDatum.{u, v} i ν family)
    (h : IsBernsteinInertiaRelated i ν family (bernsteinComponentDatum i ν family t) a)
    (ω : a.unramifiedParameter) :
    (componentEquiv h (f t)).val.val ω = (componentProductOn i ν family f a).val.val ω := by
  have ht : t = bernsteinInertialClass i ν family a :=
    (bernsteinComponentDatum_class i ν family t).symm.trans
      ((bernsteinInertialClass_eq_iff i ν family _ _).mpr h)
  subst t
  rfl

/-- Restriction evaluates at the corresponding character of the transported datum. -/
theorem componentProductHom_eval (f : BernsteinComponentProduct.{u, v} i ν family)
    (s : BernsteinInertialClass.{u, v} D.torus ν (D.standardFamily family))
    (χ : (intrinsicDatum D family s).unramifiedParameter) :
    (D.componentProductHom.{u, v} family f s).val.val χ =
      (componentProductOn i ν family f (ambientDatumAt D family s)).val.val
        (ambientParameterAt D family (intrinsicDatum D family s) χ) := by
  refine (componentProductHom_at D family f s χ).trans ?_
  unfold ambientCoordinateChange componentToAmbientDatum
  exact componentEquiv_eval_productOn family f (ambientClassAt D family s) (ambientDatumAt D family s)
    (ambientDatumAt_related D family s) (ambientParameterAt D family (intrinsicDatum D family s) χ)

set_option allowUnsafeReducibility true in
attribute [local reducible] fiberAmbientTopology canonicalTopology in
private theorem ambientFiberBound :
    ∃ B : ℕ, ∀ (K : Finset (SimpleRoot i ν)) (t : BernsteinInertialClass.{u, v} i ν family),
      Nonempty ({s // standardLeviInertialToAmbient i ν family K s = t} ↪ Fin B) := by
  have h : StandardLeviInertialFiberBoundStatement.{u, v} i ν family :=
    standardLeviInertialFiberBound.{u, v} i ν family
  unfold StandardLeviInertialFiberBoundStatement at h
  exact h

private theorem ambientGeneratorBound :
    BernsteinInvariantModuleBoundStatement.{u, v} i ν family :=
  bernsteinInvariantModuleBound.{u, v} i ν family

private theorem componentFibersBounded :
    ∃ B : ℕ, ∀ t : BernsteinInertialClass.{u, v} i ν family,
      Nonempty ({s // ambientClassAt D family s = t} ↪ Fin B) := by
  obtain ⟨B, hB⟩ := ambientFiberBound.{u, v} family
  refine ⟨B, fun t => ?_⟩
  obtain ⟨e⟩ := hB J t
  let e' : {s // ambientClassAt D family s = t} ↪
      {b // standardLeviInertialToAmbient i ν family J b = t} :=
    { toFun := fun s => ⟨D.inertialClassEmbedding family s.val,
        (ambientClassAt_eq D family s.val).symm.trans s.property⟩
      inj' := fun _ _ h => Subtype.ext ((D.inertialClassEmbedding family).injective
        (congrArg Subtype.val h)) }
  exact ⟨e'.trans e⟩

set_option maxHeartbeats 800000 in
set_option allowUnsafeReducibility true in
attribute [local reducible] invariantBoundLeviTopology canonicalTopology relativeInclusion
  inclusionAtDatum inclusionInferred invariantInclusion in
private theorem componentGeneratorsBounded :
    ∃ B : ℕ, ∀ s : BernsteinInertialClass.{u, v} D.torus ν (D.standardFamily family),
      letI := (componentHom D family s).toAlgebra
      ∃ g : Fin B → intrinsicComponent D family s,
        Submodule.span (ambientComponent family (ambientClassAt D family s)) (Set.range g) = ⊤ := by
  have hgen : BernsteinInvariantModuleBoundStatement.{u, v} i ν family := ambientGeneratorBound.{u, v} family
  unfold BernsteinInvariantModuleBoundStatement at hgen
  obtain ⟨B, hB⟩ := hgen
  refine ⟨B, fun s => ?_⟩
  let a := intrinsicDatum D family s
  let b := ambientDatumAt D family s
  let V := weylGroup (relativeLeviAt D family a) b.representation
  let inc := relativeInclusion D family a
  have h : letI := inc.toAlgebra
      ∃ g : Fin B → relativeAlgebra D family a,
        Submodule.span b.componentAlgebra (Set.range g) = ⊤ := by
    with_reducible exact hB b V (relativeWeyl_le_at D family a)
  unfold componentHom
  with_reducible
    exact @spanningFamily_comp_equiv
      (ambientComponent family (ambientClassAt D family s)) b.componentAlgebra
      (relativeAlgebra D family a) (intrinsicComponent D family s) (Fin B)
      inferInstance inferInstance inferInstance inferInstance inferInstance
      (componentToAmbientDatum D family s) inc (relativeTransport D family a).symm.toRingEquiv h

/-- The map on component products is finite, by the common generator and fiber bounds. -/
theorem componentProductHom_finite :
    RingHom.Finite
      (A := BernsteinComponentProduct.{u, v} i ν family)
      (B := BernsteinComponentProduct.{u, v} D.torus ν (D.standardFamily family))
      (D.componentProductHom.{u, v} family) := by
  unfold componentProductHom
  with_reducible
    exact @componentwiseHom_finite _ _ (ambientComponent.{u, v} family) (intrinsicComponent.{u, v} D family)
      (fun _ => inferInstance) (fun _ => inferInstance)
      (ambientClassAt.{u, v} D family) (componentHom.{u, v} D family)
      (componentFibersBounded.{u, v} D family) (componentGeneratorsBounded.{u, v} D family)

/-- Restriction is finite and evaluates at the character transported from the Levi datum. -/
def BernsteinLeviComponentProductStatement : Prop :=
  RingHom.Finite
    (A := BernsteinComponentProduct.{u, v} i ν family)
    (B := BernsteinComponentProduct.{u, v} D.torus ν (D.standardFamily family))
    (D.componentProductHom.{u, v} family) ∧
  ∀ (f : BernsteinComponentProduct.{u, v} i ν family)
    (s : BernsteinInertialClass.{u, v} D.torus ν (D.standardFamily family))
    (χ : (intrinsicDatum D family s).unramifiedParameter),
    (D.componentProductHom.{u, v} family f s).val.val χ =
      (componentProductOn i ν family f (ambientDatumAt D family s)).val.val
        (ambientParameterAt D family (intrinsicDatum D family s) χ)

theorem bernsteinLeviComponentProduct :
    D.BernsteinLeviComponentProductStatement.{u, v} family :=
  ⟨D.componentProductHom_finite.{u, v} family, D.componentProductHom_eval.{u, v} family⟩

end BernsteinLeviPresentation
end Langlands.CuspidalSupport
