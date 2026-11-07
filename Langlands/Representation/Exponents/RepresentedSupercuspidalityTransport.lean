import Langlands.Representation.Exponents.LeviSupercuspidalInductionSupport
import Langlands.GroupScheme.Rational.ParabolicAmbientTransport
import Langlands.Representation.Aubert.General.GroupTransport
import Langlands.Representation.CompactCoefficient.GroupTransport
import Langlands.Representation.CuspidalSupport.FiltrationQuasicuspidality

/-! # Transport and finite filtrations of represented supercuspidal objects

The constructions concern the actual normalized Jacquet functors. Their
vanishing depends only on the underlying coinvariant quotient.
-/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance representedTransportAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

section Isomorphism

variable {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]

local instance representedTransportSourceTopology : TopologicalSpace (rationalPoints H) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints H)] [NonarchimedeanGroup (rationalPoints H)]

/-- An ambient group-scheme isomorphism identifies the underlying vector spaces
of the two actual normalized Jacquet modules. On coefficient representatives
the map is the identity. No comparison of the normalized actions is asserted. -/
def jacquetCoinvariantsEquivOfIso
    (ε : H ≅ G) (e : rationalPoints H ≃ₜ* rationalPoints G)
    (he : ∀ x, e x = rationalPoints.map ε.hom x)
    (P M U : GroupScheme (Spec (CommRingCat.of k)))
    (p : P ⟶ H) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r))
    (A : SmoothRep.{0, u, v} ℂ (rationalPoints G)) :
    ((jacquetFunctor p l r hp hr hl hmul).obj (SmoothRep.pullback e A)) ≃ₗ[ℂ]
      ((jacquetFunctor (p ≫ ε.hom) l r (hp.comp_iso ε) hr hl hmul).obj A) := by
  let N := pointImage (r ≫ p)
  let N' := pointImage (r ≫ (p ≫ ε.hom))
  have hN : ∀ x : rationalPoints H, x ∈ N ↔ e x ∈ N' := by
    intro x
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨y, ?_⟩
      rw [he]
      rfl
    · rintro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      apply e.injective
      rw [he]
      exact hy
  exact Jacquet.Localization.transportEquiv
    (SmoothRep.pullback e A).representation A.representation N N' 1 1
    (GroupTransport.subgroupEquiv e hN).toMulEquiv
    (LinearEquiv.refl ℂ A) (fun _ _ => rfl) (fun _ => rfl)

/-- Supercuspidality transports along the actual point map of an ambient
group-scheme isomorphism. All proper actual rational parabolics are tested. -/
theorem isSupercuspidal_pullback_of_iso
    (ε : H ≅ G) (e : rationalPoints H ≃ₜ* rationalPoints G)
    (he : ∀ x, e x = rationalPoints.map ε.hom x)
    (A : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (hA : IsSupercuspidal A) :
    IsSupercuspidal (SmoothRep.pullback e A) := by
  intro P M U p l r hp hl hr hmul hproper
  have hproper' : ¬ IsIso (p ≫ ε.hom) := by
    intro h
    let := h
    apply hproper
    have hp : p = (p ≫ ε.hom) ≫ ε.inv := by simp
    rw [hp]
    infer_instance
  let := hA P M U (p ≫ ε.hom) l r (hp.comp_iso ε) hl hr hmul hproper'
  exact (jacquetCoinvariantsEquivOfIso ε e he P M U p l r hp hl hr hmul A).injective.subsingleton

end Isomorphism

section Filtration

variable {P M U : GroupScheme (Spec (CommRingCat.of k))}
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))

/-- Vanishing of an actual normalized Jacquet module is precisely vanishing of
the untwisted coinvariant quotient by the literal radical point image. -/
theorem jacquet_subsingleton_iff_coinvariants
    (A : SmoothRep.{0, u, v} ℂ (rationalPoints G)) :
    Subsingleton ((jacquetFunctor p l r hp hr hl hmul).obj A) ↔
      Subsingleton (Jacquet.Coinvariants A.representation (pointImage (r ≫ p))) := by
  change Subsingleton (Jacquet.Localization.Coinvariants A.representation
    (pointImage (r ≫ p)) 1) ↔ _
  simp only [Jacquet.Localization.Coinvariants, Jacquet.Localization.relations_one,
    Jacquet.Coinvariants, Representation.Coinvariants]

/-- A finite filtration by representations equivalent to smooth supercuspidal
objects is supercuspidal. The filtered and factor carriers have independent
universes; the graded objects need no separately supplied smoothness proof. -/
theorem isSupercuspidal_of_filtration
    {A : SmoothRep.{0, u, w} ℂ (rationalPoints G)} {m : ℕ}
    (s : ObjectRepFiltration (SmoothRep.toRep.obj A) m)
    (B : Fin m → SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (hB : ∀ i, IsSupercuspidal (B i))
    (hgraded : ∀ i, Nonempty ((s.gradedRepresentation i).ρ.Equiv (B i).representation)) :
    IsSupercuspidal A := by
  intro P M U p l r hp hl hr hmul hproper
  apply (jacquet_subsingleton_iff_coinvariants p l r hp hl hr hmul A).mpr
  apply Jacquet.coinvariants_subsingleton_of_filtration s (pointImage (r ≫ p))
  intro i
  obtain ⟨f⟩ := hgraded i
  let : Subsingleton (Jacquet.Localization.Coinvariants (B i).representation
      (pointImage (r ≫ p)) 1) := hB i P M U p l r hp hl hr hmul hproper
  have hzero : Subsingleton (Jacquet.Localization.Coinvariants
      (s.gradedRepresentation i).ρ (pointImage (r ≫ p)) 1) :=
    (Jacquet.Localization.representationEquiv (pointImage (r ≫ p)) 1 f).injective.subsingleton
  simpa only [Jacquet.Localization.Coinvariants, Jacquet.Localization.relations_one,
    Jacquet.Coinvariants, Representation.Coinvariants] using hzero

end Filtration

end Langlands.Aubert.General.RepresentedParabolic
