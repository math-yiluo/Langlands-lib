import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartCovering
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartDomain
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainCoverRefinement
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.CategoryTheory.Sites.Sheaf

/-! # Actual locally constant sheaves on finite weighted rational sites -/

noncomputable section

universe u v w

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {A : PresentedAffinoidAlgebra K}

/-- The entire locally constant function sets on the actual rational loci,
with pullback along the original locus inclusions. -/
abbrev locusLocallyConstantPresheaf (K : Type u) [NormedField K] [IsUltrametricDist K]
    (A : PresentedAffinoidAlgebra K) (C : Type w) :
    (RationalChart K A)ᵒᵖ ⥤ Type (max u w) where
  obj d := LocallyConstant d.unop.locus C
  map f := TypeCat.ofHom (LocallyConstant.comap f.unop.locusMap)
  map_id d := by
    apply ConcreteCategory.hom_ext
    intro f
    ext x
    rfl
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro h
    ext x
    rfl

/-- The corresponding entire function sets on the original quotient spectra,
with pullback along the original bounded spectrum maps. -/
abbrev spectrumLocallyConstantPresheaf (K : Type u) [NormedField K] [IsUltrametricDist K]
    (A : PresentedAffinoidAlgebra K) (C : Type w) :
    (RationalChart K A)ᵒᵖ ⥤ Type (max u w) where
  obj d := LocallyConstant (BanachSpectrum d.unop.algebra) C
  map f := TypeCat.ofHom (LocallyConstant.comap f.unop.spectrumMap)
  map_id d := by
    apply ConcreteCategory.hom_ext
    intro f
    ext x
    rfl
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro h
    ext x
    rfl

@[simp]
theorem locusLocallyConstantPresheaf_map_apply {d e : RationalChart K A}
    (q : d ⟶ e) {C : Type w} (f : LocallyConstant e.locus C) (x : d.locus) :
    (locusLocallyConstantPresheaf K A C).map q.op f x = f (q.locusMap x) := rfl

@[simp]
theorem spectrumLocallyConstantPresheaf_map_apply {d e : RationalChart K A}
    (q : d ⟶ e) {C : Type w} (f : LocallyConstant (BanachSpectrum e.algebra) C)
    (x : BanachSpectrum d.algebra) :
    (spectrumLocallyConstantPresheaf K A C).map q.op f x = f (q.spectrumMap x) := rfl

/-- Retain the original rational spectrum-locus homeomorphism in both
directions, naturally for every original bounded restriction. -/
def locallyConstantPresheafIso (K : Type u) [NormedField K] [IsUltrametricDist K]
    (A : PresentedAffinoidAlgebra K) (C : Type w) :
    locusLocallyConstantPresheaf K A C ≅ spectrumLocallyConstantPresheaf K A C :=
  NatIso.ofComponents (fun d =>
    { hom := TypeCat.ofHom (LocallyConstant.comap
        ⟨d.unop.locusHomeomorph, d.unop.locusHomeomorph.continuous⟩)
      inv := TypeCat.ofHom
        (LocallyConstant.comap
          ⟨d.unop.locusHomeomorph.symm, d.unop.locusHomeomorph.symm.continuous⟩)
      hom_inv_id := by
        apply ConcreteCategory.hom_ext
        intro f
        ext x
        exact congrArg f (d.unop.locusHomeomorph.apply_symm_apply x)
      inv_hom_id := by
        apply ConcreteCategory.hom_ext
        intro f
        ext x
        exact congrArg f (d.unop.locusHomeomorph.symm_apply_apply x) })
    (fun q => by
      apply ConcreteCategory.hom_ext
      intro f
      ext x
      exact congrArg f (q.unop.locusHomeomorph_naturality x).symm)

@[simp]
theorem locallyConstantPresheafIso_hom_apply (d : RationalChart K A) {C : Type w}
    (f : LocallyConstant d.locus C) (x : BanachSpectrum d.algebra) :
    (locallyConstantPresheafIso K A C).hom.app (Opposite.op d) f x =
      f (d.locusHomeomorph x) := rfl

@[simp]
theorem locallyConstantPresheafIso_inv_apply (d : RationalChart K A) {C : Type w}
    (f : LocallyConstant (BanachSpectrum d.algebra) C) (x : d.locus) :
    (locallyConstantPresheafIso K A C).inv.app (Opposite.op d) f x =
      f (d.locusHomeomorph.symm x) := rfl

variable [CompleteSpace K]

/-- Actual finite point covers detect local constancy. The proof uses their
original finite disjoint-union spectrum quotient, including empty covers. -/
theorem isLocallyConstant_iff_of_finite_cover {I : Type v} [Finite I]
    {d : RationalChart K A} (D : I → RationalChart K A) (f : ∀ i, D i ⟶ d)
    (hcover : ∀ x ∈ d.locus, ∃ i, x ∈ (D i).locus)
    {C : Type w} (q : d.locus → C) :
    IsLocallyConstant q ↔ ∀ i, IsLocallyConstant (q ∘ (f i).locusMap) := by
  classical
  let := Fintype.ofFinite I
  let c : Domain.FiniteCover d.toDomain :=
    Domain.FiniteCover.ofFintype (fun i => (D i).toDomain)
      (fun i => (toDomainFunctor K A).map (f i)) hcover
  constructor
  · intro h i
    exact h.comp_continuous (f i).locusMap.continuous
  · intro h s
    apply (c.isOpen_iff_loci (q ⁻¹' s)).mpr
    intro j
    exact h ((Fintype.equivFin I).symm j) s

omit [CompleteSpace K] in
/-- Extract an actual point and original restriction from any covering sieve. -/
theorem IsFiniteCovering.exists_mem {d : RationalChart K A} {R : Sieve d}
    (hR : IsFiniteCovering R) {x : BanachSpectrum A} (hx : x ∈ d.locus) :
    ∃ (e : RationalChart K A) (f : e ⟶ d), R f ∧ x ∈ e.locus := by
  obtain ⟨I, _, D, f, hf, hcover⟩ := hR
  obtain ⟨i, hi⟩ := hcover x hx
  exact ⟨D i, f i, hf i, hi⟩

variable {C : Type w} {d : RationalChart K A} {R : Sieve d}
  (p : Presieve.FamilyOfElements (locusLocallyConstantPresheaf K A C) R.arrows)
  (hp : p.Compatible)

include hp in
/-- Matching on the actual rational intersection proves equality at every
common ambient point of two sieve members. -/
theorem locusLocallyConstantCompatible_apply {e e' : RationalChart K A}
    (f : e ⟶ d) (g : e' ⟶ d) (hf : R f) (hg : R g)
    (x : BanachSpectrum A) (hx : x ∈ e.locus) (hx' : x ∈ e'.locus) :
    (p f hf : LocallyConstant e.locus C) ⟨x, hx⟩ =
      (p g hg : LocallyConstant e'.locus C) ⟨x, hx'⟩ := by
  have h := hp (interLeft e e') (interRight e e') hf hg
    (@Subsingleton.elim (Restriction (e.inter e') d) inferInstance _ _)
  let y : (e.inter e').locus := ⟨x, by rw [locus_inter]; exact ⟨hx, hx'⟩⟩
  exact congrArg (fun q : LocallyConstant (e.inter e').locus C => q y) h

include hp in
/-- Point coverage constructs the unique compatible coefficient value.
No coefficient element or nonemptiness is supplied. -/
theorem exists_locusLocallyConstantSieveValue (hR : IsFiniteCovering R) (x : d.locus) :
    ∃ c : C, ∀ (e : RationalChart K A) (f : e ⟶ d) (hf : R f)
      (hx : x.val ∈ e.locus), c = (p f hf : LocallyConstant e.locus C) ⟨x.val, hx⟩ := by
  obtain ⟨e, f, hf, hx⟩ := hR.exists_mem x.property
  refine ⟨(p f hf : LocallyConstant e.locus C) ⟨x.val, hx⟩, ?_⟩
  intro e' g hg hx'
  exact locusLocallyConstantCompatible_apply p hp f g hf hg x.val hx hx'

/-- Choose the uniquely determined local value at each actual target point. -/
def locusLocallyConstantSieveGlueFun (hR : IsFiniteCovering R) : d.locus → C :=
  fun x => (exists_locusLocallyConstantSieveValue p hp hR x).choose

theorem locusLocallyConstantSieveGlueFun_apply (hR : IsFiniteCovering R)
    {e : RationalChart K A} (f : e ⟶ d) (hf : R f)
    (x : d.locus) (hx : x.val ∈ e.locus) :
    locusLocallyConstantSieveGlueFun p hp hR x =
      (p f hf : LocallyConstant e.locus C) ⟨x.val, hx⟩ :=
  (exists_locusLocallyConstantSieveValue p hp hR x).choose_spec e f hf hx

/-- The actual finite-cover quotient criterion makes the glued function
locally constant in the original target subspace topology. -/
def locusLocallyConstantSieveGlue (hR : IsFiniteCovering R) : LocallyConstant d.locus C where
  toFun := locusLocallyConstantSieveGlueFun p hp hR
  isLocallyConstant := by
    obtain ⟨I, hI, D, f, hf, hcover⟩ := hR
    let : Finite I := hI
    apply (isLocallyConstant_iff_of_finite_cover D f hcover _).mpr
    intro i
    have he : (locusLocallyConstantSieveGlueFun p hp
        ⟨I, hI, D, f, hf, hcover⟩ ∘ (f i).locusMap) =
          ⇑(p (f i) (hf i) : LocallyConstant (D i).locus C) := by
      funext x
      exact locusLocallyConstantSieveGlueFun_apply p hp _ (f i) (hf i) _ x.property
    exact (congrArg IsLocallyConstant he).mpr
      (p (f i) (hf i) : LocallyConstant (D i).locus C).isLocallyConstant

@[simp]
theorem locusLocallyConstantSieveGlue_apply (hR : IsFiniteCovering R)
    {e : RationalChart K A} (f : e ⟶ d) (hf : R f) (x : e.locus) :
    locusLocallyConstantSieveGlue p hp hR (f.locusMap x) =
      (p f hf : LocallyConstant e.locus C) x :=
  locusLocallyConstantSieveGlueFun_apply p hp hR f hf _ x.property

/-- The constructed gluing is the only function with all original restrictions. -/
theorem locusLocallyConstantSieveGlue_unique (hR : IsFiniteCovering R)
    (q : LocallyConstant d.locus C)
    (hq : p.IsAmalgamation q) : q = locusLocallyConstantSieveGlue p hp hR := by
  ext x
  obtain ⟨e, f, hf, hx⟩ := hR.exists_mem x.property
  have he := congrArg (fun s : LocallyConstant e.locus C => s ⟨x.val, hx⟩) (hq f hf)
  exact he.trans (locusLocallyConstantSieveGlueFun_apply p hp hR f hf x hx).symm

/-- Every compatible family on every finite-point-covering sieve admits
exactly one actual locally constant amalgamation. -/
theorem locusLocallyConstantPresheaf_isSheaf (K : Type u) [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] (A : PresentedAffinoidAlgebra K) (C : Type w) :
    Presheaf.IsSheaf (finiteRationalTopology K A) (locusLocallyConstantPresheaf K A C) := by
  rw [isSheaf_iff_isSheaf_of_type]
  intro d R hR p hp
  refine ⟨locusLocallyConstantSieveGlue p hp hR, ?_, ?_⟩
  · intro e f hf
    ext x
    exact locusLocallyConstantSieveGlue_apply p hp hR f hf x
  · intro q hq
    exact locusLocallyConstantSieveGlue_unique p hp hR q hq

/-- The unchanged quotient-spectrum presheaf is a sheaf via the original
natural rational spectrum-locus homeomorphism. -/
theorem spectrumLocallyConstantPresheaf_isSheaf (K : Type u) [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] (A : PresentedAffinoidAlgebra K) (C : Type w) :
    Presheaf.IsSheaf (finiteRationalTopology K A)
      (spectrumLocallyConstantPresheaf K A C) :=
  (Presheaf.isSheaf_of_iso_iff (locallyConstantPresheafIso K A C)).mp
    (locusLocallyConstantPresheaf_isSheaf K A C)

/-- The full locally constant sheaf on actual rational locus subspaces. -/
def locusLocallyConstantSheaf (K : Type u) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] (A : PresentedAffinoidAlgebra K) (C : Type w) :
    Sheaf (finiteRationalTopology K A) (Type (max u w)) :=
  ⟨locusLocallyConstantPresheaf K A C, locusLocallyConstantPresheaf_isSheaf K A C⟩

/-- The full locally constant sheaf on original rational quotient spectra. -/
def spectrumLocallyConstantSheaf (K : Type u) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] (A : PresentedAffinoidAlgebra K) (C : Type w) :
    Sheaf (finiteRationalTopology K A) (Type (max u w)) :=
  ⟨spectrumLocallyConstantPresheaf K A C, spectrumLocallyConstantPresheaf_isSheaf K A C⟩

/-- The original natural rational homeomorphism identifies the two
constructed sheaves, retaining all bounded restrictions and both point maps. -/
def locallyConstantSheafIso (K : Type u) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] (A : PresentedAffinoidAlgebra K) (C : Type w) :
    locusLocallyConstantSheaf K A C ≅ spectrumLocallyConstantSheaf K A C :=
  ObjectProperty.isoMk _ (locallyConstantPresheafIso K A C)

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
