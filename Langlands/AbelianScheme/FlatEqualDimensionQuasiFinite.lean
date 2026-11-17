import Langlands.AbelianScheme.IsogenySpecialization
import Langlands.AbelianScheme.StructureCohomologyVanishing
import Langlands.AbelianScheme.FieldAbelianSchemeGeometry
import Langlands.GroupScheme.DominantHomFlat
import Langlands.AlgebraicGeometry.SmoothReducedProof
import Langlands.AlgebraicGeometry.FieldSmoothClosedPointStalkDimensionProof
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Sober

/-! # Surjective endomorphisms of abelian varieties are isogenies

A flat morphism of finite type is quasi-finite at every closed point where the local rings of
source and target have the same finite Krull dimension: by the dimension formula for flat
local homomorphisms, the closed fibre of the local rings is zero-dimensional. A surjective
endomorphism of an abelian variety over an algebraically closed field is flat, so it is
quasi-finite at every closed point, hence everywhere, hence finite: it is an isogeny.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

namespace Langlands.AlgebraicGeometry.FlatEqualDimension

/-- The Krull dimension of the local ring of a scheme at a point. -/
def stalkDimension (X : Scheme.{u}) (x : X) : WithBot ℕ∞ :=
  ringKrullDim (X.presheaf.stalk x)

/-- For a flat local homomorphism of noetherian local rings of the same finite Krull dimension,
the only prime lying over the maximal ideal of the source is the maximal ideal of the target. -/
theorem eq_maximalIdeal_of_comap_eq {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] [IsNoetherianRing R] [IsNoetherianRing S] [Algebra R S] [Module.Flat R S]
    [IsLocalHom (algebraMap R S)] {g : ℕ} (hR : ringKrullDim R = g) (hS : ringKrullDim S = g)
    (Q : Ideal S) [Q.IsPrime]
    (hQ : Q.comap (algebraMap R S) = IsLocalRing.maximalIdeal R) :
    Q = IsLocalRing.maximalIdeal S := by
  set p := IsLocalRing.maximalIdeal R
  set P := IsLocalRing.maximalIdeal S
  have hlies : P.LiesOver p := ⟨(IsLocalRing.maximalIdeal_comap (algebraMap R S)).symm⟩
  have hform := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p P
  have hP : P.height = g := by
    have h := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := S)
    rw [hS] at h
    exact_mod_cast h
  have hp : p.height = g := by
    have h := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R)
    rw [hR] at h
    exact_mod_cast h
  let I := p.map (algebraMap R S)
  have hIP : I ≤ P :=
    Ideal.map_le_iff_le_comap.mpr (IsLocalRing.maximalIdeal_comap (algebraMap R S)).ge
  have hIQ : I ≤ Q := Ideal.map_le_iff_le_comap.mpr hQ.ge
  have hPmap : (P.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by simpa using hIP)
  have hQmap : (Q.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by simpa using hIQ)
  have h0 : (P.map (Ideal.Quotient.mk I)).height = 0 := by
    rw [hP, hp] at hform
    generalize (P.map (Ideal.Quotient.mk I)).height = h at hform
    induction h using ENat.recTopCoe with
    | top => simp at hform
    | coe n =>
      have : (g : ℕ∞) = ((g + n : ℕ) : ℕ∞) := by push_cast; exact hform
      have := Nat.cast_injective this
      simp only [Nat.cast_eq_zero]
      omega
  have hmin := (Ideal.height_eq_zero_iff (I := P.map (Ideal.Quotient.mk I))).mp h0
  have hQP : Q ≤ P := IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)
  have hle : P.map (Ideal.Quotient.mk I) ≤ Q.map (Ideal.Quotient.mk I) :=
    hmin.2 ⟨hQmap, bot_le⟩ (Ideal.map_mono hQP)
  refine le_antisymm hQP ?_
  have := Ideal.comap_mono (f := Ideal.Quotient.mk I) hle
  rwa [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective,
    Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
    sup_eq_left.mpr hIP, sup_eq_left.mpr hIQ] at this

/-- In a noetherian quasi-sober space, a closed point with no proper generization is open. -/
theorem isOpen_singleton_of_forall_specializes {X : Type*} [TopologicalSpace X]
    [NoetherianSpace X] [QuasiSober X] {x : X} (hx : IsClosed ({x} : Set X))
    (hgen : ∀ z, z ⤳ x → z = x) : IsOpen ({x} : Set X) := by
  have hfin := NoetherianSpace.finite_irreducibleComponents (α := X)
  have heq : ({x} : Set X)ᶜ = ⋃ C ∈ {C ∈ irreducibleComponents X | x ∉ C}, C := by
    ext z
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_ofPred_eq,
      exists_prop]
    constructor
    · intro hz
      refine ⟨irreducibleComponent z, ⟨irreducibleComponent_mem_irreducibleComponents z, ?_⟩,
        mem_irreducibleComponent⟩
      intro hxC
      have hirr : IsIrreducible (irreducibleComponent z) := isIrreducible_irreducibleComponent
      have hcl : IsClosed (irreducibleComponent z) := isClosed_irreducibleComponent
      have hη := hirr.isGenericPoint_genericPoint_closure
      rw [hcl.closure_eq] at hη
      have hηx : hirr.genericPoint ⤳ x := hη.specializes hxC
      have hηeq := hgen _ hηx
      have hC : irreducibleComponent z = {x} := by
        rw [← hη.def, hηeq, hx.closure_eq]
      exact hz (by simpa [hC] using (mem_irreducibleComponent (x := z)))
    · rintro ⟨C, ⟨-, hxC⟩, hzC⟩ rfl
      exact hxC hzC
  rw [← isClosed_compl_iff, heq]
  exact hfin.subset (fun C hC => hC.1) |>.isClosed_biUnion fun C hC =>
    isClosed_of_mem_irreducibleComponents C hC.1

/-- Let `f` be flat and let `x` be a point whose local ring has the same finite Krull dimension
as the local ring at `f x`. Then no other generization of `x` lies in the fibre of `x`. -/
theorem eq_of_specializes_of_apply_eq {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] {x z : X}
    [IsNoetherianRing (X.presheaf.stalk x)] [IsNoetherianRing (Y.presheaf.stalk (f x))]
    {g : ℕ} (hX : stalkDimension X x = g) (hY : stalkDimension Y (f x) = g) (hzx : z ⤳ x)
    (hfz : f z = f x) :
    z = x := by
  obtain ⟨q, rfl⟩ : z ∈ Set.range (X.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]
    exact hzx
  have hcomp : Y.fromSpecStalk (f x) (Spec.map (f.stalkMap x) q) = f (X.fromSpecStalk x q) := by
    rw [← Scheme.Hom.comp_apply, Scheme.SpecMap_stalkMap_fromSpecStalk, Scheme.Hom.comp_apply]
  rw [hfz] at hcomp
  have hq : Spec.map (f.stalkMap x) q = IsLocalRing.closedPoint _ :=
    (Y.fromSpecStalk (f x)).isEmbedding.injective
      (hcomp.trans (Scheme.fromSpecStalk_closedPoint (x := f x)).symm)
  have hcomap : q.asIdeal.comap (f.stalkMap x).hom =
      IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x)) :=
    congrArg PrimeSpectrum.asIdeal hq
  algebraize [(f.stalkMap x).hom]
  have : Module.Flat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    Flat.stalkMap f x
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  have := q.isPrime
  have hmax := eq_maximalIdeal_of_comap_eq hY hX q.asIdeal hcomap
  have : q = IsLocalRing.closedPoint _ := PrimeSpectrum.ext hmax
  rw [this, Scheme.fromSpecStalk_closedPoint]

/-- A flat morphism of finite type from a noetherian scheme is quasi-finite at every closed point
whose local ring has the same finite Krull dimension as the local ring at its image. -/
theorem quasiFiniteAt_of_ringKrullDim_eq {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    [LocallyOfFiniteType f] [NoetherianSpace X] {x : X} (hx : IsClosed ({x} : Set X))
    [IsNoetherianRing (X.presheaf.stalk x)] [IsNoetherianRing (Y.presheaf.stalk (f x))]
    {g : ℕ} (hX : stalkDimension X x = g) (hY : stalkDimension Y (f x) = g) :
    f.QuasiFiniteAt x := by
  have : NoetherianSpace (f.fiber (f x)) :=
    (noetherianSpace_iff_of_homeomorph (f.fiberHomeo (f x))).mpr inferInstance
  rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber]
  have hset : ({f.asFiber x} : Set (f.fiber (f x))) = f.fiberι (f x) ⁻¹' {x} := by
    ext w
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · rintro rfl
      exact Scheme.Hom.fiberι_asFiber f x
    · intro hw
      apply (f.fiberι (f x)).isEmbedding.injective
      rw [hw, Scheme.Hom.fiberι_asFiber]
  refine isOpen_singleton_of_forall_specializes ?_ fun w hw => ?_
  · rw [hset]
    exact hx.preimage (f.fiberι (f x)).continuous
  · have hw' : f.fiberι (f x) w ⤳ x := by
      simpa using hw.map (f.fiberι (f x)).continuous
    have hfw : f (f.fiberι (f x) w) = f x := by
      have := (f.fiberHomeo (f x) w).2
      simpa using this
    have := eq_of_specializes_of_apply_eq f hX hY hw' hfw
    have hmem : w ∈ f.fiberι (f x) ⁻¹' {x} := this
    rw [← hset] at hmem
    exact hmem

end Langlands.AlgebraicGeometry.FlatEqualDimension

namespace Langlands.AbelianScheme.SurjectiveIsogeny

open Langlands.AlgebraicGeometry.FlatEqualDimension

/-- A surjective endomorphism of an abelian scheme over an algebraically closed field is an
isogeny. -/
theorem isIsogeny_of_surjective {k : Type u} [Field k] [IsAlgClosed k]
    {A : AbelianScheme (Spec (CommRingCat.of k))} (α : A ⟶ A) (hα : Surjective (hom α)) :
    IsIsogeny α := by
  obtain ⟨g, hg⟩ := exists_hasRelativeDimension_of_field A
  have := field_isNoetherian A
  have := field_isIntegral A
  have hw : hom α ≫ A.X.hom = A.X.hom := Over.w (groupHom α).hom.hom
  have : IsProper (hom α ≫ A.X.hom) := by rw [hw]; infer_instance
  have : IsProper (hom α) := .of_comp _ A.X.hom
  have : IsReduced A.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k A.X.left
      A.X.hom
  have : IsDominant (hom α) := ⟨hα.surj.denseRange⟩
  have hflat : Flat (hom α) := Langlands.GroupScheme.DominantHomFlat.flat_of_isDominant
    (groupHom α)
  have hdim : ∀ x : A.X.left, IsClosed ({x} : Set A.X.left) →
      stalkDimension A.X.left x = g := fun x hx =>
    Langlands.AlgebraicGeometry.fieldSmoothClosedPointStalkDimension k A.X.left A.X.hom g hg x hx
  have hqf : ∀ x : A.X.left, IsClosed ({x} : Set A.X.left) → (hom α).QuasiFiniteAt x := by
    intro x hx
    have hfx : IsClosed ({hom α x} : Set A.X.left) := by
      simpa using (hom α).isClosedMap _ hx
    exact quasiFiniteAt_of_ringKrullDim_eq (hom α) hx (hdim x hx) (hdim _ hfx)
  have hLQF : LocallyQuasiFinite (hom α) := by
    rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff, eq_top_iff]
    intro z _
    obtain ⟨c, hc, hcl⟩ := (isClosed_closure (s := ({z} : Set A.X.left))).exists_closed_singleton
      ⟨z, subset_closure rfl⟩
    have hzc : z ⤳ c := specializes_iff_mem_closure.mpr hc
    exact hzc.mem_open (hom α).quasiFiniteLocus.isOpen (hqf c hcl)
  have hfin : IsFinite (hom α) := IsFinite.of_isProper_of_locallyQuasiFinite _
  exact (isIsogeny_iff α).mpr ⟨hfin, hflat, hα⟩

end Langlands.AbelianScheme.SurjectiveIsogeny
