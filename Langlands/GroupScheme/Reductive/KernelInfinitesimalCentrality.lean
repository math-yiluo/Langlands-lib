import Langlands.GroupScheme.Torus.MultiplicativeTypeSubgroupInfinitesimalLiftStatement
import Langlands.GroupScheme.Torus.MultiplicativeTypeInfinitesimalCentralityStatement
import Langlands.AbelianScheme.KernelBaseChange
import Langlands.GroupScheme.Rational.CentralSubgroupGeometry
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-! # Kernel centrality through nilpotent base thickenings -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.GroupScheme
namespace KernelInfinitesimalCentrality

variable {S S₀ : Scheme.{u}} {G H : GroupScheme S}

/-- Centrality of a pulled-back kernel is centrality of the pulled-back inclusion. -/
theorem isCentral_kernel_baseChange_iff (i : S₀ ⟶ S) (f : G ⟶ H) :
    IsCentral (kernelι ((GroupScheme.baseChange i).map f)) ↔
      IsCentral ((GroupScheme.baseChange i).map (kernelι f)) := by
  constructor
  · intro hc
    have hc' := hc.comp (kernelBaseChangeIso i f).hom
    simpa only [kernelBaseChangeIso_hom_ι] using hc'
  · intro hc
    have hc' := hc.comp (kernelBaseChangeIso i f).inv
    simpa only [kernelBaseChangeIso_inv_ι] using hc'

/-- The actual kernel comparison transports multiplicative type in both directions. -/
theorem isMultiplicativeType_kernel_baseChange_iff (i : S₀ ⟶ S) (f : G ⟶ H) :
    RelativeMultiplicativeType.IsMultiplicativeType
      (kernel ((GroupScheme.baseChange i).map f)) ↔
      RelativeMultiplicativeType.IsMultiplicativeType
        ((GroupScheme.baseChange i).obj (kernel f)) := by
  constructor
  · exact RelativeMultiplicativeType.IsMultiplicativeType.of_iso (kernelBaseChangeIso i f)
  · exact RelativeMultiplicativeType.IsMultiplicativeType.of_iso (kernelBaseChangeIso i f).symm

/-- The ideal sheaf of `Spec (A/J) → Spec A` is locally nilpotent if `J` is nilpotent. -/
theorem quotient_locallyNilpotent (A : Type u) [CommRing A] (J : Ideal A)
    (hJ : IsNilpotent J) :
    ∀ x : Spec (CommRingCat.of A),
      ∃ U : (Spec (CommRingCat.of A)).affineOpens,
        x ∈ (U : (Spec (CommRingCat.of A)).Opens) ∧
          IsNilpotent ((Spec.algebraMap A (A ⧸ J)).ker.ideal U) := by
  let r := Spec.algebraMap A (A ⧸ J)
  have hker : (RingHom.ker r.appTop.hom).comap (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom = J := by
    rw [RingHom.comap_ker]
    change RingHom.ker (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ r.appTop).hom) = J
    rw [← Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk J))]
    change RingHom.ker ((Scheme.ΓSpecIso (CommRingCat.of (A ⧸ J))).inv.hom.comp
      (Ideal.Quotient.mk J)) = J
    rw [RingHom.ker_comp_of_injective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ J))).inv).1,
      Ideal.mk_ker]
  have hker' : RingHom.ker r.appTop.hom =
      Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom J := by
    conv_rhs => rw [← hker]
    exact (Ideal.map_comap_of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).2 _).symm
  intro x
  refine ⟨⟨⊤, isAffineOpen_top _⟩, trivial, ?_⟩
  change IsNilpotent (r.ker.ideal _)
  rw [Scheme.ker_of_isAffine, Scheme.IdealSheafData.ofIdealTop_ideal, hker']
  obtain ⟨n, hn⟩ := hJ
  exact ⟨n, by rw [← Ideal.map_pow, ← Ideal.map_pow, hn]; simp⟩

/-- Under the two infinitesimal input propositions, a flat immersed subgroup of a
smooth group is central and of multiplicative type if its nilpotent reduction is. -/
theorem subgroup_of_nilpotent_reduction
    (hlift : MultiplicativeTypeSubgroupInfinitesimalLiftStatement.{u})
    (hcentral : MultiplicativeTypeInfinitesimalCentralityStatement.{u})
    (A : Type u) [CommRing A] (J : Ideal A) (hJ : IsNilpotent J)
    (K G : GroupScheme (Spec (CommRingCat.of A))) [Smooth G.X.hom]
    (k : K ⟶ G) (hk : IsImmersion k.hom.hom.left) (hflat : Flat K.X.hom)
    (hmt : RelativeMultiplicativeType.IsMultiplicativeType
      ((GroupScheme.baseChange (Spec.algebraMap A (A ⧸ J))).obj K))
    (hc : IsCentral ((GroupScheme.baseChange (Spec.algebraMap A (A ⧸ J))).map k)) :
    RelativeMultiplicativeType.IsMultiplicativeType K ∧ IsCentral k := by
  have hm := (hlift A J hJ G).2.1 K k hk hflat hmt
  have : IsClosedImmersion (Spec.algebraMap A (A ⧸ J)) := by
    change IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
    exact IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  exact ⟨hm, hcentral _ _ _ (quotient_locallyNilpotent A J hJ) K G hm k hc⟩

/-- The preceding adapter for the actual scheme-theoretic kernel. Its flatness
comes from flatness of the homomorphism by the kernel pullback square. -/
theorem kernel_of_nilpotent_reduction
    (hlift : MultiplicativeTypeSubgroupInfinitesimalLiftStatement.{u})
    (hcentral : MultiplicativeTypeInfinitesimalCentralityStatement.{u})
    (A : Type u) [CommRing A] (J : Ideal A) (hJ : IsNilpotent J)
    (G H : GroupScheme (Spec (CommRingCat.of A)))
    [Smooth G.X.hom] [IsSeparated H.X.hom] (f : G ⟶ H) [Flat f.hom.hom.left]
    (hmt : RelativeMultiplicativeType.IsMultiplicativeType
      (kernel ((GroupScheme.baseChange (Spec.algebraMap A (A ⧸ J))).map f)))
    (hc : IsCentral (kernelι
      ((GroupScheme.baseChange (Spec.algebraMap A (A ⧸ J))).map f))) :
    RelativeMultiplicativeType.IsMultiplicativeType (kernel f) ∧
      IsCentral (kernelι f) := by
  have hkflat : Flat (kernel f).X.hom :=
    MorphismProperty.of_isPullback (kernel_isPullback_scheme f) inferInstance
  exact subgroup_of_nilpotent_reduction hlift hcentral A J hJ (kernel f) G
    (kernelι f) inferInstance hkflat
    ((isMultiplicativeType_kernel_baseChange_iff _ f).1 hmt)
    ((isCentral_kernel_baseChange_iff _ f).1 hc)

/-- The unchanged actual kernel, regarded as a commutative group scheme using the
centrality obtained from its nilpotent reduction. The two infinitesimal results
remain explicit input hypotheses. -/
def centralKernelOfNilpotentReduction
    (hlift : MultiplicativeTypeSubgroupInfinitesimalLiftStatement.{u})
    (hcentral : MultiplicativeTypeInfinitesimalCentralityStatement.{u})
    (A : Type u) [CommRing A] (J : Ideal A) (hJ : IsNilpotent J)
    (G H : GroupScheme (Spec (CommRingCat.of A)))
    [Smooth G.X.hom] [IsSeparated H.X.hom] (f : G ⟶ H) [Flat f.hom.hom.left]
    (hmt : RelativeMultiplicativeType.IsMultiplicativeType
      (kernel ((GroupScheme.baseChange (Spec.algebraMap A (A ⧸ J))).map f)))
    (hc : IsCentral (kernelι
      ((GroupScheme.baseChange (Spec.algebraMap A (A ⧸ J))).map f))) :
    CommGroupScheme (Spec (CommRingCat.of A)) :=
  (kernel_of_nilpotent_reduction hlift hcentral A J hJ G H f hmt hc).2.commGroupScheme

@[simp]
theorem centralKernelOfNilpotentReduction_toGrp
    (hlift : MultiplicativeTypeSubgroupInfinitesimalLiftStatement.{u})
    (hcentral : MultiplicativeTypeInfinitesimalCentralityStatement.{u})
    (A : Type u) [CommRing A] (J : Ideal A) (hJ : IsNilpotent J)
    (G H : GroupScheme (Spec (CommRingCat.of A)))
    [Smooth G.X.hom] [IsSeparated H.X.hom] (f : G ⟶ H) [Flat f.hom.hom.left]
    (hmt : RelativeMultiplicativeType.IsMultiplicativeType
      (kernel ((GroupScheme.baseChange (Spec.algebraMap A (A ⧸ J))).map f)))
    (hc : IsCentral (kernelι
      ((GroupScheme.baseChange (Spec.algebraMap A (A ⧸ J))).map f))) :
    (centralKernelOfNilpotentReduction hlift hcentral A J hJ G H f hmt hc).toGrp =
      kernel f := rfl

end KernelInfinitesimalCentrality
end Langlands.GroupScheme
