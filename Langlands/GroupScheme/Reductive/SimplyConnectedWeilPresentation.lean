import Langlands.GroupScheme.Reductive.AdjointWeilPresentation
import Langlands.GroupScheme.AffineWeilFiniteFamily
import Langlands.GroupScheme.Reductive.GeometricSimplyConnected
import Langlands.GroupScheme.Reductive.AdjointWeilPairRecovery
import Langlands.GroupScheme.Reductive.AffineWeilPairEtaleDescentStatement

/-! # Actual simply connected Weil presentations and conditional pair descent -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

/-- Simple connectedness at a geometric fibre reflects from any specified
point over it in a base change. -/
theorem isSimplyConnected_geometricFiber_of_baseChange_at
    {S T : Scheme.{u}} (G : GroupScheme S) (b : T ⟶ S) (t : T)
    (h : IsSimplyConnected (geometricFiber ((baseChange b).obj G) t)) :
    IsSimplyConnected (geometricFiber G (b t)) := by
  have hcomp := h.of_iso (baseChangeCompIso b (geometricPoint T t) G)
  have hfield := (fieldSimplyConnected_iff_geometricFiber G (geometricPoint T t ≫ b)).mp hcomp
  have himage : (geometricPoint T t ≫ b)
      (IsLocalRing.closedPoint (AlgebraicClosure (T.residueField t))) = b t := by
    change b (T.fromSpecResidueField t _) = b t
    rw [Scheme.fromSpecResidueField_apply]
  rwa [himage] at hfield

namespace AffineWeilPairRecovery

/-- The actual local tensor-algebra recoveries of a covering family reflect
simply connected geometric fibres of the descended factor group. -/
theorem isFibrewiseSimplyConnected
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    {J : Type u} (R D : J → Type u) [∀ i, CommRing (R i)] [∀ i, Algebra A (R i)]
    [∀ i, CommRing (D i)] [∀ i, Algebra (R i) (D i)]
    (e : ∀ i, R i ⊗[A] B ≃ₐ[R i] D i)
    (G : GroupScheme (Spec (CommRingCat.of B)))
    (H : ∀ i, GroupScheme (Spec (CommRingCat.of (D i))))
    (hcover : ∀ s : Spec (CommRingCat.of A), ∃ i,
      s ∈ Set.range (algebraBaseMap A (R i)))
    (he : ∀ i, Nonempty ((baseChange (map A B R D e i)).obj G ≅ H i))
    (hH : ∀ i, IsFibrewiseSimplyConnected (H i)) : IsFibrewiseSimplyConnected G := by
  intro t
  obtain ⟨i, s, rfl⟩ := covers A B R D e hcover t
  obtain ⟨f⟩ := he i
  have hlocal : IsSimplyConnected (geometricFiber ((baseChange (map A B R D e i)).obj G) s) :=
    (hH i s).of_iso ((baseChange (geometricPoint _ s)).mapIso f)
  exact isSimplyConnected_geometricFiber_of_baseChange_at G (map A B R D e i) s hlocal

end AffineWeilPairRecovery

variable {A : Type u} [CommRing A]

/-- An actual finite étale Weil presentation with simply connected
almost-simple geometric factor fibres and a surjective finite base. -/
structure AffineSimplyConnectedWeilPresentation (G : GroupScheme (Spec (CommRingCat.of A))) where
  ring : Type u
  [commRing : CommRing ring]
  [algebra : Algebra A ring]
  [finite : Module.Finite A ring]
  [projective : Module.Projective A ring]
  [etale : Algebra.Etale A ring]
  group : GroupScheme (Spec (CommRingCat.of ring))
  [isAffine : IsAffine group.X.left]
  [locallyOfFiniteType : LocallyOfFiniteType group.X.hom]
  surjective : Surjective (algebraBaseMap A ring)
  reductive : IsReductive group
  fibres : ∀ s : Spec (CommRingCat.of ring),
    IsSimplyConnected (geometricFiber group s) ∧ IsAlmostSimple (geometricFiber group s)
  iso : G ≅ AffineWeil.groupScheme A ring group

attribute [instance] AffineSimplyConnectedWeilPresentation.commRing
  AffineSimplyConnectedWeilPresentation.algebra AffineSimplyConnectedWeilPresentation.finite
  AffineSimplyConnectedWeilPresentation.projective AffineSimplyConnectedWeilPresentation.etale
  AffineSimplyConnectedWeilPresentation.isAffine AffineSimplyConnectedWeilPresentation.locallyOfFiniteType

namespace AffineSimplyConnectedWeilPresentation

variable {G H : GroupScheme (Spec (CommRingCat.of A))}

/-- Precompose a presentation with an actual isomorphism of its original group. -/
def precompose (P : AffineSimplyConnectedWeilPresentation H) (e : G ≅ H) :
    AffineSimplyConnectedWeilPresentation G where
  ring := P.ring
  group := P.group
  surjective := P.surjective
  reductive := P.reductive
  fibres := P.fibres
  iso := e ≪≫ P.iso

/-- The supplied data imply exactly the target's existential presentation. -/
theorem exists_pair (P : AffineSimplyConnectedWeilPresentation G) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B) (_ : Module.Finite A B)
      (_ : Module.Projective A B) (_ : Algebra.Etale A B)
      (G' : GroupScheme (Spec (CommRingCat.of B))) (_ : IsAffine G'.X.left)
      (_ : LocallyOfFiniteType G'.X.hom),
      Surjective (algebraBaseMap A B) ∧ IsReductive G' ∧
      (∀ s : Spec (CommRingCat.of B),
        IsSimplyConnected (geometricFiber G' s) ∧ IsAlmostSimple (geometricFiber G' s)) ∧
      Nonempty (G ≅ AffineWeil.groupScheme A B G') :=
  ⟨P.ring, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    P.group, inferInstance, inferInstance, P.surjective, P.reductive, P.fibres, ⟨P.iso⟩⟩

/-- A supplied finite product of reductive groups with simply connected
almost-simple geometric fibres gives an actual Weil presentation. -/
def ofProduct {I : Type u} [Finite I]
    (F : I → GroupScheme (Spec (CommRingCat.of A))) (e : G ≅ pi F)
    (hnt : HasNontrivialGeometricFibres G) (hred : ∀ i, IsReductive (F i))
    (hSC : ∀ i, IsFibrewiseSimplyConnected (F i))
    (hAS : ∀ i s, IsAlmostSimple (geometricFiber (F i) s)) :
    AffineSimplyConnectedWeilPresentation G := by
  let : ∀ i, IsAffine (F i).X.left :=
    fun i => @isAffine_of_isAffineHom _ _ (F i).X.hom (hred i).isAffineHom inferInstance
  let : ∀ i, Smooth (F i).X.hom := fun i => (hred i).smooth
  let : ∀ i, LocallyOfFiniteType (F i).X.hom := fun _ => inferInstance
  have hsc : IsFibrewiseSimplyConnected (AffineWeil.FiniteFamily.group A I F) :=
    AffineWeil.FiniteFamily.geometricFiber_property A I F (fun _ _ G => IsSimplyConnected G)
      (fun _ _ _ _ e h => h.of_iso e)
      (fun _ _ _ _ _ _ h => (isSimplyConnected_fieldExtension_iff _).mp h) hSC
  exact
    { ring := I → A
      group := AffineWeil.FiniteFamily.group A I F
      surjective := AffineAdjointWeilPresentation.surjective_productBase F e hnt
      reductive := AffineWeil.FiniteFamily.isReductive A I F hred
      fibres := fun s => ⟨hsc s, AffineWeil.FiniteFamily.isFibrewiseAlmostSimple A I F hAS s⟩
      iso := e ≪≫ AffineWeil.FiniteFamily.iso A I F }

/-- Assuming generic almost-simple pair descent, actual local simply
connected presentations descend, with simple connectedness recovered on the
original tensor-base comparisons. -/
def ofEtaleLocal (hD : AffineWeilPairEtaleDescentStatement.{u})
    (G : GroupScheme (Spec (CommRingCat.of A)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    {J : Type u} (R : J → Type u) [∀ i, CommRing (R i)] [∀ i, Algebra A (R i)]
    [∀ i, Algebra.Etale A (R i)]
    (P : ∀ i, AffineSimplyConnectedWeilPresentation
      ((baseChange (algebraBaseMap A (R i))).obj G))
    (hcover : ∀ s : Spec (CommRingCat.of A), ∃ i,
      s ∈ Set.range (algebraBaseMap A (R i))) : AffineSimplyConnectedWeilPresentation G := by
  apply Classical.choice
  obtain ⟨B, hB, hAB, hfin, hproj, het, G', haff, hlft,
      hsurj, hred, hAS, hiso, hrec⟩ :=
    hD A G J R (fun i => (P i).ring) (fun i => (P i).group) hcover
      (fun i => (P i).surjective) (fun i => (P i).reductive)
      (fun i s => ((P i).fibres s).2) (fun i => ⟨(P i).iso⟩)
  let : CommRing B := hB
  let : Algebra A B := hAB
  let : Module.Finite A B := hfin
  let : Module.Projective A B := hproj
  let : Algebra.Etale A B := het
  let : IsAffine G'.X.left := haff
  let : LocallyOfFiniteType G'.X.hom := hlft
  let E (i : J) : R i ⊗[A] B ≃ₐ[R i] (P i).ring := Classical.choose (hrec i)
  have hsc : IsFibrewiseSimplyConnected G' := by
    apply AffineWeilPairRecovery.isFibrewiseSimplyConnected A B R (fun i => (P i).ring)
      E G' (fun i => (P i).group) hcover
    · intro i
      rw [AffineWeilPairRecovery.map_eq]
      exact Classical.choose_spec (hrec i)
    · intro i s
      exact ((P i).fibres s).1
  exact ⟨{ ring := B
           group := G'
           surjective := hsurj
           reductive := hred
           fibres := fun s => ⟨hsc s, hAS s⟩
           iso := Classical.choice hiso }⟩

end AffineSimplyConnectedWeilPresentation

end Langlands.GroupScheme
