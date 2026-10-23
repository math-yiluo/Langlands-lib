import Langlands.Geometry.Analytic.StrictTestDomain.RationalEquivalence
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.Topology.Algebra.MulAction

/-! # Bounded automorphisms acting on rational domains and sections -/

noncomputable section

universe u

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {P : PresentedStrictAffinoidAlgebra K}

/-- An automorphism in the category of actual presented algebras gives a bounded
algebra equivalence, retaining the specified forward and inverse maps. -/
def boundedEquiv (g : Aut P) : BoundedAlgEquiv K P P :=
  BoundedAlgEquiv.ofHomInv g.hom g.inv
    (fun a => congrArg (fun f : BoundedAlgHom K P P => f a) g.hom_inv_id)
    (fun a => congrArg (fun f : BoundedAlgHom K P P => f a) g.inv_hom_id)

@[simp] theorem boundedEquiv_hom (g : Aut P) :
    (boundedEquiv g).toBoundedAlgHom = g.hom := by ext a; rfl

/-- Apply the forward algebra automorphism to the chosen rational inputs. -/
instance rationalMulAction : MulAction (Aut P) (RationalData K P) where
  smul g d := d.pullback g.hom
  one_smul d := d.pullback_id
  mul_smul g h d := d.pullback_comp h.hom g.hom

@[simp] theorem smul_rational (g : Aut P) (d : RationalData K P) :
    g • d = d.pullback g.hom := rfl

/-- The inverse algebra map makes contravariant spectrum transport a left action. -/
instance spectrumMulAction : MulAction (Aut P) (BanachSpectrum P) where
  smul g x := BanachSpectrum.comap g.inv.toBoundedRingHom x
  one_smul _x := BanachSpectrum.ext fun _ => rfl
  mul_smul _g _h _x := BanachSpectrum.ext fun _ => rfl

@[simp] theorem smul_spectrum_apply (g : Aut P) (x : BanachSpectrum P) (a : P) :
    (g • x) a = x (g.inv.toAlgHom a) := rfl

/-- Each individual operator is continuous; no topology on the operator group
or joint continuity of a group action is asserted. -/
instance spectrumContinuousConstSMul : ContinuousConstSMul (Aut P) (BanachSpectrum P) where
  continuous_const_smul g := (BanachSpectrum.comapContinuous g.inv.toBoundedRingHom).continuous

/-- Simultaneously moving a rational presentation and a point preserves incidence. -/
theorem smul_mem_smul_locus_iff (g : Aut P) (d : RationalData K P)
    (x : BanachSpectrum P) : (g • x) ∈ (g • d).locus ↔ x ∈ d.locus := by
  change BanachSpectrum.comap g.hom.toBoundedRingHom
    (BanachSpectrum.comap g.inv.toBoundedRingHom x) ∈ d.locus ↔ x ∈ d.locus
  have heq : BanachSpectrum.comap g.hom.toBoundedRingHom
      (BanachSpectrum.comap g.inv.toBoundedRingHom x) = x := by
    apply BanachSpectrum.ext
    intro a
    exact congrArg (fun f : BoundedAlgHom K P P => x (f a)) g.hom_inv_id
  rw [heq]

/-- The moved rational locus is exactly the image under the point action. -/
theorem locus_smul (g : Aut P) (d : RationalData K P) :
    (g • d).locus = (fun x : BanachSpectrum P => g • x) '' d.locus := by
  ext x
  constructor
  · intro hx
    refine ⟨g⁻¹ • x, ?_, smul_inv_smul g x⟩
    exact (smul_mem_smul_locus_iff g d (g⁻¹ • x)).mp (by simpa using hx)
  · rintro ⟨y, hy, rfl⟩
    exact (smul_mem_smul_locus_iff g d y).mpr hy

/-- Arbitrary point-covering families, including empty ones, are invariant. -/
theorem familyCovers_smul_iff (g : Aut P) {I : Type u}
    (d : RationalData K P) (D : I → RationalData K P) :
    RationalData.FamilyCovers (g • d) (fun i => g • D i) ↔
      RationalData.FamilyCovers d D := by
  simpa only [smul_rational, boundedEquiv_hom] using
    RationalData.familyCovers_pullback_equiv_iff (boundedEquiv g) d D

/-- Operators transport both rational objects and their locus inclusions. -/
def actionFunctor (g : Aut P) : RationalData K P ⥤ RationalData K P :=
  RationalData.pullbackFunctor g.hom

@[simp] theorem actionFunctor_one :
    actionFunctor (1 : Aut P) = 𝟭 (RationalData K P) :=
  RationalData.pullbackFunctor_id

/-- Categorical composition lists the first applied functor first. -/
theorem actionFunctor_mul (g h : Aut P) :
    actionFunctor (g * h) = actionFunctor h ⋙ actionFunctor g :=
  RationalData.pullbackFunctor_comp h.hom g.hom

variable [CompleteSpace K]

instance actionFunctor_isContinuous (g : Aut P) :
    (actionFunctor g).IsContinuous
      (RationalData.finiteRationalTopology K P) (RationalData.finiteRationalTopology K P) :=
  RationalData.pullbackFunctor_isContinuous g.hom

/-- The actual algebra presheaf is carried to itself along each operator. -/
def presheafIso (g : Aut P) :
    RationalData.rationalPresheaf K P ≅
      (actionFunctor g).op ⋙ RationalData.rationalPresheaf K P := by
  simpa only [actionFunctor, boundedEquiv_hom] using RationalData.rationalPresheafIso (boundedEquiv g)

/-- The total space of algebraic sections retains the chosen rational
presentation and an actual element of its constructed quotient algebra. -/
def TotalSections (P : PresentedStrictAffinoidAlgebra K) :=
  (d : RationalData K P) × d.algebra

/-- Move a section using the actual bounded quotient comparison. -/
def sectionMap (g : Aut P) (s : TotalSections P) : TotalSections P :=
  ⟨g • s.1, s.1.comparison g.hom s.2⟩

private theorem comparison_comp (d : RationalData K P)
    (f k : BoundedAlgHom K P P) :
    d.comparison (k.comp f) =
      ((d.pullback f).comparison k).comp (d.comparison f) := by
  apply d.hom_ext
  apply BoundedAlgHom.ext
  intro a
  have h₁ := congrArg (fun q => q a) (d.comparison_comp_baseMap (k.comp f))
  have h₂ := congrArg (fun q => q (f a)) ((d.pullback f).comparison_comp_baseMap k)
  have h₃ := congrArg (fun q => q a) (d.comparison_comp_baseMap f)
  exact h₁.trans (h₂.symm.trans
    (congrArg (fun z => (d.pullback f).comparison k z) h₃.symm))

private theorem comparison_id (d : RationalData K P) :
    d.comparison (BoundedAlgHom.id K P) = BoundedAlgHom.id K d.algebra := by
  apply d.hom_ext
  exact d.comparison_comp_baseMap (BoundedAlgHom.id K P)

@[simp] theorem sectionMap_one (s : TotalSections P) : sectionMap 1 s = s := by
  rcases s with ⟨d, a⟩
  exact congrArg (fun f : BoundedAlgHom K d.algebra d.algebra =>
    (⟨d, f a⟩ : TotalSections P)) (comparison_id d)

private theorem comparison_comp_section (d : RationalData K P)
    (f k : BoundedAlgHom K P P) (a : d.algebra) :
    (⟨d.pullback (k.comp f), d.comparison (k.comp f) a⟩ : TotalSections P) =
      ⟨(d.pullback f).pullback k, (d.pullback f).comparison k (d.comparison f a)⟩ := by
  change (⟨d.pullback (k.comp f), d.comparison (k.comp f) a⟩ :
    (e : RationalData K P) × e.algebra) =
      ⟨(d.pullback f).pullback k, (d.pullback f).comparison k (d.comparison f a)⟩
  apply Sigma.ext (d.pullback_comp f k)
  exact heq_of_eq (congrArg (fun q => q a) (comparison_comp d f k))

@[simp] theorem sectionMap_mul (g h : Aut P) (s : TotalSections P) :
    sectionMap (g * h) s = sectionMap g (sectionMap h s) :=
  comparison_comp_section s.1 h.hom g.hom s.2

/-- The comparison maps obey the group laws on actual quotient sections. -/
instance sectionsMulAction : MulAction (Aut P) (TotalSections P) where
  smul := sectionMap
  one_smul := sectionMap_one
  mul_smul := sectionMap_mul

@[simp] theorem smul_section_domain (g : Aut P) (s : TotalSections P) :
    (g • s).1 = g • s.1 := rfl

/-- Section transport commutes with restriction along every rational inclusion. -/
theorem restriction_transport {d e : RationalData K P} (h : d ⟶ e)
    (g : Aut P) (a : e.algebra) :
    ((actionFunctor g).map h).restriction (e.comparison g.hom a) =
      d.comparison g.hom (h.restriction a) :=
  congrArg (fun f => f a) (h.restriction_pullback_comp_comparison g.hom)

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism
