import Langlands.GroupScheme.Reductive.ConnectedFibreLocusFibres
import Langlands.GroupScheme.Reductive.ConnectedFibreLocusDvrCore
import Langlands.GroupScheme.HomScheme.SmoothAffineGroupFiniteTypeModel
import Langlands.AlgebraicGeometry.NoetherianDvrSpecialization

/-! # Reduction of the closedness of the connected-fibre locus to discrete valuation rings -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace ConnectedFibreLocus

/-- A locally constructible subset of a scheme that is stable under specialization is
closed. -/
theorem isClosed_of_isLocallyConstructible_of_stableUnderSpecialization {S : Scheme.{u}}
    {Y : Set S} (hc : IsLocallyConstructible Y) (hs : StableUnderSpecialization Y) :
    IsClosed Y := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro s hsY
  obtain ⟨U, hU, hsU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := s) (U := ⊤) (by trivial)
  have he : IsOpenEmbedding hU.fromSpec := hU.fromSpec.isOpenEmbedding
  have hcl : IsClosed (hU.fromSpec ⁻¹' Y) := by
    apply PrimeSpectrum.isClosed_of_stableUnderSpecialization_of_isConstructible
    · intro x y hxy hx
      exact hs (hxy.map hU.fromSpec.continuous) hx
    · exact (hc.preimage_of_isOpenEmbedding he).isConstructible
  obtain ⟨x, rfl⟩ : s ∈ Set.range hU.fromSpec := by rwa [hU.range_fromSpec]
  refine ⟨hU.fromSpec '' (hU.fromSpec ⁻¹' Y)ᶜ, ?_, he.isOpenMap _ hcl.isOpen_compl,
    ⟨x, hsY, rfl⟩⟩
  rintro _ ⟨z, hz, rfl⟩ hY
  exact hz hY

/-- The connected-fibre locus is invariant under isomorphism of group schemes. -/
theorem connectedFibreLocus_of_iso {S : Scheme.{u}} {G H : GroupScheme S} (e : G ≅ H) :
    connectedFibreLocus G = connectedFibreLocus H := by
  ext s
  exact connectedSpace_iff_of_iso ((baseChange (S.fromSpecResidueField s)).mapIso e)

/-- The reductive identity-component locus is invariant under isomorphism of smooth affine
group schemes. -/
theorem identityComponentReductiveLocus_of_iso {S : Scheme.{u}} {G H : GroupScheme S}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [Smooth H.X.hom] [IsAffineHom H.X.hom]
    (e : G ≅ H) :
    identityComponentReductiveLocus G = identityComponentReductiveLocus H := by
  ext s
  constructor
  · intro h
    exact IsConnectedReductive.of_iso
      (IdentityComponent.mapIso ((baseChange (geometricPoint S s)).mapIso e.symm)) h
  · intro h
    exact IsConnectedReductive.of_iso
      (IdentityComponent.mapIso ((baseChange (geometricPoint S s)).mapIso e)) h

/-- A point of the spectrum of the ring of a discrete-valuation-ring point with zero prime
ideal maps to the generic endpoint. -/
theorem dvrSpecialization_map_of_eq_bot {X : Scheme.{u}} {η s : X}
    (d : Langlands.AlgebraicGeometry.DvrSpecialization X η s) (p : Spec d.ring)
    (hp : p.asIdeal = ⊥) : d.map p = η := by
  have h : p = (⟨⊥, inferInstance⟩ : PrimeSpectrum d.ring) := PrimeSpectrum.ext hp
  subst h
  exact d.generic_image

/-- A point of the spectrum of the ring of a discrete-valuation-ring point with maximal
prime ideal maps to the closed endpoint. -/
theorem dvrSpecialization_map_of_eq_maximalIdeal {X : Scheme.{u}} {η s : X}
    (d : Langlands.AlgebraicGeometry.DvrSpecialization X η s) (p : Spec d.ring)
    (hp : p.asIdeal = IsLocalRing.maximalIdeal d.ring) : d.map p = s := by
  have h : p = IsLocalRing.closedPoint d.ring := PrimeSpectrum.ext hp
  subst h
  exact d.closed_image

/-- The discrete-valuation-ring step: connectedness of fibres passes along a specialization
realized by a discrete valuation ring, provided the local statement holds. -/
theorem mem_connectedFibreLocus_of_dvrSpecialization (hcore : DvrCoreStatement.{u})
    {X : Scheme.{u}} (H : GroupScheme X) [Smooth H.X.hom] [IsAffineHom H.X.hom]
    {η s : X} (d : Langlands.AlgebraicGeometry.DvrSpecialization X η s)
    (hη : η ∈ identityComponentReductiveLocus H) (hs : s ∈ identityComponentReductiveLocus H)
    (hconn : η ∈ connectedFibreLocus H) : s ∈ connectedFibreLocus H := by
  let R : Type u := d.ring
  let K := FractionRing R
  let G' : GroupScheme (Spec (CommRingCat.of R)) := (baseChange d.map).obj H
  have hgen : d.map ((algebraBaseMap R K) (IsLocalRing.closedPoint K)) = η := by
    apply dvrSpecialization_map_of_eq_bot
    show Ideal.comap (algebraMap R K) (IsLocalRing.maximalIdeal K) = ⊥
    rw [IsLocalRing.maximalIdeal_eq_bot]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)
  have hcl : d.map ((algebraBaseMap R (IsLocalRing.ResidueField R))
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField R))) = s := by
    apply dvrSpecialization_map_of_eq_maximalIdeal
    have h : PrimeSpectrum.comap (IsLocalRing.residue R)
        (IsLocalRing.closedPoint (IsLocalRing.ResidueField R)) = IsLocalRing.closedPoint R :=
      IsLocalRing.comap_closedPoint (IsLocalRing.residue R)
    exact congrArg PrimeSpectrum.asIdeal h
  have key : ∀ p : Spec (CommRingCat.of R), d.map p ∈ identityComponentReductiveLocus H := by
    intro p
    by_cases hp : p.asIdeal = ⊥
    · rw [dvrSpecialization_map_of_eq_bot d p hp]
      exact hη
    · rw [dvrSpecialization_map_of_eq_maximalIdeal d p
        (IsLocalRing.eq_maximalIdeal (Ring.DimensionLEOne.maximalOfPrime hp p.isPrime))]
      exact hs
  have hloc : identityComponentReductiveLocus G' = Set.univ := by
    rw [identityComponentReductiveLocus_baseChange]
    ext p
    simp only [Set.mem_preimage, Set.mem_univ, iff_true]
    exact key p
  have hconn' : d.map ((algebraBaseMap R K) (IsLocalRing.closedPoint K)) ∈
      connectedFibreLocus H := by
    rw [hgen]
    exact hconn
  have hK : ConnectedSpace ((baseChange (algebraBaseMap R K)).obj G').X.left := by
    rw [connectedSpace_fieldPoint_iff, connectedFibreLocus_baseChange, Set.mem_preimage]
    exact hconn'
  have hk := hcore R K G' hloc hK
  rw [connectedSpace_fieldPoint_iff, connectedFibreLocus_baseChange, Set.mem_preimage] at hk
  have hk' : d.map ((algebraBaseMap R (IsLocalRing.ResidueField R))
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField R))) ∈ connectedFibreLocus H := hk
  rw [hcl] at hk'
  exact hk'

/-- Over an affine base, connectedness of fibres passes to specializations. -/
theorem mem_connectedFibreLocus_of_specializes_affine (hcore : DvrCoreStatement.{u})
    (A : Type u) [CommRing A] (G : GroupScheme (Spec (CommRingCat.of A)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (hG : identityComponentReductiveLocus G = Set.univ)
    {t s : Spec (CommRingCat.of A)} (hts : t ⤳ s) (ht : t ∈ connectedFibreLocus G) :
    s ∈ connectedFibreLocus G := by
  obtain ⟨R₀, _, _, φ, G₀, hsm, haf, ⟨e⟩⟩ := exists_finiteType_model A G
  have : IsNoetherianRing R₀ := Algebra.FiniteType.isNoetherianRing ℤ R₀
  let p : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R₀) :=
    Spec.map (CommRingCat.ofHom φ)
  have hloc : ∀ x, p x ∈ identityComponentReductiveLocus G₀ := by
    intro x
    have h := identityComponentReductiveLocus_baseChange G₀ p
    rw [← identityComponentReductiveLocus_of_iso e, hG] at h
    have hx : x ∈ p ⁻¹' identityComponentReductiveLocus G₀ := by
      rw [← h]
      trivial
    exact hx
  have hconn : ∀ x, x ∈ connectedFibreLocus G ↔ p x ∈ connectedFibreLocus G₀ := by
    intro x
    rw [connectedFibreLocus_of_iso e, connectedFibreLocus_baseChange]
    rfl
  rw [hconn] at ht ⊢
  by_cases hne : p t = p s
  · rwa [← hne]
  obtain ⟨d⟩ := Langlands.AlgebraicGeometry.nonempty_dvrSpecialization
    (Spec (CommRingCat.of R₀)) (p t) (p s) (hts.map p.continuous) hne
  exact mem_connectedFibreLocus_of_dvrSpecialization hcore G₀ d (hloc t) (hloc s) ht

/-- Connectedness of fibres passes to specializations. -/
theorem stableUnderSpecialization_connectedFibreLocus (hcore : DvrCoreStatement.{u})
    {S : Scheme.{u}} (G : GroupScheme S) [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (hG : identityComponentReductiveLocus G = Set.univ) :
    StableUnderSpecialization (connectedFibreLocus G) := by
  intro t s hts ht
  obtain ⟨U, hU, hsU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := s) (U := ⊤) (by trivial)
  have htU : t ∈ U := hts.mem_open U.isOpen hsU
  obtain ⟨s', rfl⟩ : s ∈ Set.range hU.fromSpec := by rwa [hU.range_fromSpec]
  obtain ⟨t', rfl⟩ : t ∈ Set.range hU.fromSpec := by rwa [hU.range_fromSpec]
  have hts' : t' ⤳ s' := hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff.mp hts
  have hGA : identityComponentReductiveLocus ((baseChange hU.fromSpec).obj G) = Set.univ := by
    rw [identityComponentReductiveLocus_baseChange, hG]
    rfl
  have ht' : t' ∈ connectedFibreLocus ((baseChange hU.fromSpec).obj G) := by
    rw [connectedFibreLocus_baseChange]
    exact ht
  have hs' := mem_connectedFibreLocus_of_specializes_affine hcore Γ(S, U)
    ((baseChange hU.fromSpec).obj G) hGA hts' ht'
  rw [connectedFibreLocus_baseChange] at hs'
  exact hs'

/-- **Reduction.** The local statement over discrete valuation rings implies Conrad's
Proposition 3.1.12. -/
theorem connectedFibreLocusClosed_of_dvrCore (hcore : DvrCoreStatement.{u}) :
    ConnectedFibreLocusClosedStatement.{u} := by
  intro S G _ _ hG
  have hclosed : IsClosed (connectedFibreLocus G) :=
    isClosed_of_isLocallyConstructible_of_stableUnderSpecialization
      (isLocallyConstructible_connectedFibreLocus G)
      (stableUnderSpecialization_connectedFibreLocus hcore G hG)
  refine ⟨hclosed, ?_⟩
  intro η hη hconn s
  exact (hη.specializes (Set.mem_univ s)).mem_closed hclosed hconn

end ConnectedFibreLocus

end Langlands.GroupScheme
