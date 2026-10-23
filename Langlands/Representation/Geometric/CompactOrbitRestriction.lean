import Langlands.Representation.Geometric.OrbitRestriction

/-! Compact orbit restriction from an actual orbit homeomorphism. -/

noncomputable section
open CategoryTheory

namespace Langlands.Geometric

universe uR uG uV

private theorem compact_preimage_relativelyClosed
    {X : Type*} [TopologicalSpace X] {U Z K : Set X}
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hZ : IsClosed ((fun x : U => (x : X)) ⁻¹' Z)) :
    IsCompact ((fun x : Z => (x : X)) ⁻¹' K) := by
  have hKU' : K ⊆ Set.range (fun x : U => (x : X)) := by
    simpa only [Subtype.range_coe] using hKU
  have hK' : IsCompact ((fun x : U => (x : X)) ⁻¹' K) :=
    Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hK hKU'
  have hI := (hK'.inter_right hZ).image continuous_subtype_val
  have himage : (fun x : U => (x : X)) ''
      (((fun x : U => (x : X)) ⁻¹' K) ∩ ((fun x : U => (x : X)) ⁻¹' Z)) =
      K ∩ Z := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hKU hx.1⟩, hx, rfl⟩
  rw [himage] at hI
  apply Subtype.isCompact_iff.mpr
  simpa only [Set.image_preimage_eq_inter_range, Subtype.range_coe] using hI

variable {R : Type uR} [CommRing R]
  {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module R V]

omit [IsTopologicalGroup G] in
/-- Under an orbit homeomorphism with the actual representative formula,
the support of restriction is precisely the inverse image of ambient support. -/
theorem quotientSupport_smoothOrbitRestriction (P Q : Subgroup G) (w : G)
    (e : Induction.LeftQuotient (orbitStabilizer P Q w) ≃ₜ cosetOrbit P Q w)
    (he : ∀ q : Q, (e (Induction.quotientMap (orbitStabilizer P Q w) q)).val =
      Induction.quotientMap P (w⁻¹ * (q : G)))
    (σ : Representation R P V) (f : Induction.SmoothFunctions P σ) :
    Induction.quotientSupport (orbitStabilizer P Q w)
        (Induction.eval _ _ (smoothOrbitRestriction P Q w σ f)) =
      (fun x => (e x).val) ⁻¹' Induction.quotientSupport P (Induction.eval P σ f) := by
  ext x
  induction x using Quotient.inductionOn with
  | h q =>
    have hsource := Set.ext_iff.mp
      (Induction.quotientMap_preimage_quotientSupport (orbitStabilizer P Q w)
        (σ.comp (stabilizerToInducing P Q w)) (smoothOrbitRestriction P Q w σ f)) q
    have htarget := Set.ext_iff.mp
      (Induction.quotientMap_preimage_quotientSupport P σ f) (w⁻¹ * (q : G))
    change (Induction.quotientMap (orbitStabilizer P Q w) q ∈
      Induction.quotientSupport (orbitStabilizer P Q w)
        (Induction.eval _ _ (smoothOrbitRestriction P Q w σ f))) ↔
      (e (Induction.quotientMap (orbitStabilizer P Q w) q)).val ∈
        Induction.quotientSupport P (Induction.eval P σ f)
    rw [he q]
    exact hsource.trans htarget.symm

/-- A compact ambient section supported in a set where the orbit is relatively
closed restricts to a compact section on that orbit. -/
theorem isCompact_quotientSupport_smoothOrbitRestriction
    (P Q : Subgroup G) (w : G)
    (e : Induction.LeftQuotient (orbitStabilizer P Q w) ≃ₜ cosetOrbit P Q w)
    (he : ∀ q : Q, (e (Induction.quotientMap (orbitStabilizer P Q w) q)).val =
      Induction.quotientMap P (w⁻¹ * (q : G)))
    (U : Set (Induction.LeftQuotient P))
    (hZ : IsClosed ((fun x : U => (x : Induction.LeftQuotient P)) ⁻¹'
      cosetOrbit P Q w))
    (σ : Representation R P V) (f : Induction.CompactFunctions P σ)
    (hf : ∀ x : G, Induction.eval P σ f.val x ≠ 0 →
      Induction.quotientMap P x ∈ U) :
    IsCompact (Induction.quotientSupport (orbitStabilizer P Q w)
      (Induction.eval _ _ (smoothOrbitRestriction P Q w σ f.val))) := by
  rw [quotientSupport_smoothOrbitRestriction P Q w e he]
  have hKU : Induction.quotientSupport P (Induction.eval P σ f.val) ⊆ U := by
    rintro x ⟨y, hy, rfl⟩
    exact hf y hy
  exact e.isClosedEmbedding.isCompact_preimage
    (compact_preimage_relativelyClosed f.property hKU hZ)

/-- The actual compact restriction, retaining the same evaluation formula. -/
def compactOrbitRestriction (P Q : Subgroup G) (w : G)
    (e : Induction.LeftQuotient (orbitStabilizer P Q w) ≃ₜ cosetOrbit P Q w)
    (he : ∀ q : Q, (e (Induction.quotientMap (orbitStabilizer P Q w) q)).val =
      Induction.quotientMap P (w⁻¹ * (q : G)))
    (U : Set (Induction.LeftQuotient P))
    (hZ : IsClosed ((fun x : U => (x : Induction.LeftQuotient P)) ⁻¹'
      cosetOrbit P Q w))
    (σ : Representation R P V) (f : Induction.CompactFunctions P σ)
    (hf : ∀ x : G, Induction.eval P σ f.val x ≠ 0 →
      Induction.quotientMap P x ∈ U) :
    Induction.CompactFunctions (orbitStabilizer P Q w)
      (σ.comp (stabilizerToInducing P Q w)) :=
  ⟨smoothOrbitRestriction P Q w σ f.val,
    isCompact_quotientSupport_smoothOrbitRestriction P Q w e he U hZ σ f hf⟩

@[simp]
theorem compactOrbitRestriction_eval (P Q : Subgroup G) (w : G)
    (e : Induction.LeftQuotient (orbitStabilizer P Q w) ≃ₜ cosetOrbit P Q w)
    (he : ∀ q : Q, (e (Induction.quotientMap (orbitStabilizer P Q w) q)).val =
      Induction.quotientMap P (w⁻¹ * (q : G)))
    (U : Set (Induction.LeftQuotient P))
    (hZ : IsClosed ((fun x : U => (x : Induction.LeftQuotient P)) ⁻¹'
      cosetOrbit P Q w))
    (σ : Representation R P V) (f : Induction.CompactFunctions P σ)
    (hf : ∀ x : G, Induction.eval P σ f.val x ≠ 0 →
      Induction.quotientMap P x ∈ U) (q : Q) :
    Induction.eval _ _ (compactOrbitRestriction P Q w e he U hZ σ f hf).val q =
      Induction.eval P σ f.val (w⁻¹ * (q : G)) := rfl

/-- Compact restriction is natural on every invariant ambient support set
where the orbit is relatively closed. -/
def supportOrbitRestrictionNat (P Q : Subgroup G) (w : G)
    (e : Induction.LeftQuotient (orbitStabilizer P Q w) ≃ₜ cosetOrbit P Q w)
    (he : ∀ q : Q, (e (Induction.quotientMap (orbitStabilizer P Q w) q)).val =
      Induction.quotientMap P (w⁻¹ * (q : G)))
    (U : Set (Induction.LeftQuotient P))
    (hU : ∀ (q : Q) (x : Induction.LeftQuotient P), x ∈ U →
      Induction.quotientRight P (q : G) x ∈ U)
    (hZ : IsClosed ((fun x : U => (x : Induction.LeftQuotient P)) ⁻¹'
      cosetOrbit P Q w)) :
    (supportSubfunctor.{uR, uG, uV} (R := R) P Q U hU).toFunctor ⟶
      orbitPiece P Q w where
  app A := Rep.ofHom
    { toLinearMap :=
        { toFun := fun f => compactOrbitRestriction P Q w e he U hZ A.obj.ρ f.val f.property
          map_add' _ _ := rfl
          map_smul' _ _ := rfl }
      isIntertwining' q := by
        ext f x
        change Induction.eval P A.obj.ρ f.val.val ((w⁻¹ * (x : G)) * (q : G)) =
          Induction.eval P A.obj.ρ f.val.val (w⁻¹ * ((x : G) * (q : G)))
        rw [mul_assoc] }
  naturality _ _ _ := rfl

@[simp]
theorem supportOrbitRestrictionNat_eval (P Q : Subgroup G) (w : G)
    (e : Induction.LeftQuotient (orbitStabilizer P Q w) ≃ₜ cosetOrbit P Q w)
    (he : ∀ q : Q, (e (Induction.quotientMap (orbitStabilizer P Q w) q)).val =
      Induction.quotientMap P (w⁻¹ * (q : G)))
    (U : Set (Induction.LeftQuotient P))
    (hU : ∀ (q : Q) (x : Induction.LeftQuotient P), x ∈ U →
      Induction.quotientRight P (q : G) x ∈ U)
    (hZ : IsClosed ((fun x : U => (x : Induction.LeftQuotient P)) ⁻¹'
      cosetOrbit P Q w))
    (A : Induction.SmoothRep.{uR, uG, uV} R P)
    (f : (supportSubfunctor (R := R) P Q U hU).representation A) (q : Q) :
    Induction.eval _ _ (((supportOrbitRestrictionNat P Q w e he U hU hZ).app A).hom f).val q =
      Induction.eval P A.obj.ρ f.val.val (w⁻¹ * (q : G)) := rfl

namespace OrderedDoubleCosets

variable {P Q : Subgroup G} {n : ℕ}

/-- The natural compact restriction on an upper support step. -/
def supportStepOrbitRestriction (s : OrderedDoubleCosets P Q n) (i : Fin n)
    (e : Induction.LeftQuotient (orbitStabilizer P Q (s.representative i)) ≃ₜ
      cosetOrbit P Q (s.representative i))
    (he : ∀ q : Q, (e (Induction.quotientMap (orbitStabilizer P Q (s.representative i)) q)).val =
      Induction.quotientMap P ((s.representative i)⁻¹ * (q : G))) :
    ((s.supportFiltration (R := R)).step i.succ).toFunctor ⟶
      orbitPiece.{uR, uG, uV} (R := R) P Q (s.representative i) :=
  supportOrbitRestrictionNat P Q (s.representative i) e he (s.initialOrbits i.succ)
    (fun q _ hx => s.initialOrbits_right_invariant i.succ q hx)
    (s.cosetOrbit_isClosed_in_next i)

/-- Its kernel is exactly the actual pulled-back preceding support step. -/
theorem supportStepOrbitRestriction_kernel (s : OrderedDoubleCosets P Q n) (i : Fin n)
    (e : Induction.LeftQuotient (orbitStabilizer P Q (s.representative i)) ≃ₜ
      cosetOrbit P Q (s.representative i))
    (he : ∀ q : Q, (e (Induction.quotientMap (orbitStabilizer P Q (s.representative i)) q)).val =
      Induction.quotientMap P ((s.representative i)⁻¹ * (q : G)))
    (A : Induction.SmoothRep.{uR, uG, uV} R P)
    (f : ((s.supportFiltration (R := R)).step i.succ).representation A) :
    f ∈ ((s.supportFiltration (R := R)).step i.castSucc).lowerInUpper
        ((s.supportFiltration (R := R)).step i.succ) A ↔
      ((s.supportStepOrbitRestriction i e he).app A).hom f = 0 := by
  change (∀ x : G, Induction.eval P A.obj.ρ f.val.val x ≠ 0 →
    Induction.quotientMap P x ∈ s.initialOrbits i.castSucc) ↔ _
  rw [← s.orbitRestriction_zero_iff_lowerSupport i A.obj.ρ f.val.val f.property]
  constructor
  · intro h
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext q
    exact h q
  · intro h q
    exact congrArg (fun g : Induction.CompactFunctions (orbitStabilizer P Q (s.representative i))
      (A.obj.ρ.comp (stabilizerToInducing P Q (s.representative i))) =>
        Induction.eval _ _ g.val q) h

end OrderedDoubleCosets

end Langlands.Geometric
