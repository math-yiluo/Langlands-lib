import Langlands.GroupScheme.Torus.IsomorphismLocus
import Langlands.GroupScheme.Torus.FieldPointMaximality

/-! # Detecting split-torus embeddings and isomorphisms on a local special fibre -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

namespace TorusLocalSpecialization

/-- The specified homomorphism becomes an isomorphism on the special fibre
of the local base, taken along its residue quotient homomorphism. -/
def IsSpecialFibreIsomorphism
    {R : Type u} [CommRing R] [IsLocalRing R]
    {G H : GroupScheme (Spec (CommRingCat.of R))} (f : G ⟶ H) : Prop :=
  IsIso ((baseChange
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).map f)

/-- An open immersion into the spectrum of a local ring is an isomorphism if
its image contains the closed point. -/
theorem isIso_openImmersion_of_closedPoint_mem
    {R : Type u} [CommRing R] [IsLocalRing R]
    {V : Scheme.{u}} (q : V ⟶ Spec (CommRingCat.of R)) [IsOpenImmersion q]
    (hq : IsLocalRing.closedPoint R ∈ Set.range q) : IsIso q := by
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top q
  exact (IsLocalRing.closedPoint_mem_iff q.opensRange).mp hq

/-- A residue-field point factoring through an open immersion forces its image
to contain the closed point of the local base. -/
theorem isIso_openImmersion_of_residue_factorization
    {R : Type u} [CommRing R] [IsLocalRing R]
    {V : Scheme.{u}} (q : V ⟶ Spec (CommRingCat.of R)) [IsOpenImmersion q]
    (x : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶ V)
    (hx : x ≫ q = Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) : IsIso q := by
  apply isIso_openImmersion_of_closedPoint_mem q
  refine ⟨x (IsLocalRing.closedPoint (IsLocalRing.ResidueField R)), ?_⟩
  have h := congrArg (fun f : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶
      Spec (CommRingCat.of R) =>
        f (IsLocalRing.closedPoint (IsLocalRing.ResidueField R))) hx
  change q (x _) = PrimeSpectrum.comap (IsLocalRing.residue R) _ at h
  exact h.trans (IsLocalRing.comap_closedPoint (IsLocalRing.residue R))

/-- Base change along an isomorphism reflects closed subgroup embeddings. -/
theorem isClosedSubgroup_of_isIso_baseChange
    {S S' : Scheme.{u}} (b : S' ⟶ S) [IsIso b]
    {H G : GroupScheme S} (i : H ⟶ G)
    (hi : IsClosedSubgroup ((baseChange b).map i)) : IsClosedSubgroup i := by
  have : IsClosedImmersion ((baseChange b).map i).hom.hom.left := hi
  have hp := TorusIsomorphismLocus.underlying_isPullback b i
  apply (MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)
    (pullback.fst H.X.hom b) i.hom.hom.left).mp
  rw [hp.w]
  infer_instance

/-- A split-torus homomorphism into an affine group over a local ring is a
closed immersion if its residue-field specialization is a closed immersion. -/
theorem isClosedSubgroup_of_specialFibre
    {R : Type u} [CommRing R] [IsLocalRing R]
    {T G : GroupScheme (Spec (CommRingCat.of R))}
    (hT : IsSplitTorus T) [IsAffineHom G.X.hom] (i : T ⟶ G)
    (hi : IsClosedSubgroup ((baseChange
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).map i)) :
    IsClosedSubgroup i := by
  obtain ⟨V, q, hq, x, hx, hiq⟩ := exists_open_isClosedImmersion_baseChange hT i
    (IsLocalRing.ResidueField R)
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) hi
  let := hq
  have := isIso_openImmersion_of_residue_factorization q x hx
  exact isClosedSubgroup_of_isIso_baseChange q i hiq

/-- A homomorphism between split tori over a local ring is an isomorphism if
its residue-field specialization is an isomorphism. -/
theorem isIso_of_specialFibre
    {R : Type u} [CommRing R] [IsLocalRing R]
    {T Q : GroupScheme (Spec (CommRingCat.of R))}
    (hT : IsSplitTorus T) (hQ : IsSplitTorus Q) (f : T ⟶ Q)
    (hf : IsIso ((baseChange
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).map f)) : IsIso f := by
  obtain ⟨V, q, hq, x, hx, hfq⟩ := TorusIsomorphismLocus.exists_open_affine hT hQ f
    (IsLocalRing.ResidueField R)
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) hf
  let := hq
  have := isIso_openImmersion_of_residue_factorization q x hx
  let := hfq
  exact isIso_of_baseChange q f

/-- If a homomorphism is an isomorphism on the special fibre, its composite
with any closed split-torus embedding is a closed embedding over the local base. -/
theorem isClosedSubgroup_comp_of_specialFibreIso
    {R : Type u} [CommRing R] [IsLocalRing R]
    {T G H : GroupScheme (Spec (CommRingCat.of R))}
    (hT : IsSplitTorus T) [IsAffineHom H.X.hom]
    (i : T ⟶ G) (hi : IsClosedSubgroup i) (f : G ⟶ H)
    (hf : IsIso ((baseChange
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).map f)) :
    IsClosedSubgroup (i ≫ f) := by
  apply isClosedSubgroup_of_specialFibre hT
  rw [Functor.map_comp]
  have : IsClosedImmersion ((baseChange
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).map i).hom.hom.left :=
    hi.baseChange _
  let := hf
  change IsClosedImmersion
    (((baseChange (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).map i).hom.hom.left ≫
      ((baseChange (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).map f).hom.hom.left)
  infer_instance

end TorusLocalSpecialization

end Langlands.GroupScheme
