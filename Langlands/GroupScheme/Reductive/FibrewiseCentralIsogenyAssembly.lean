import Langlands.GroupScheme.Reductive.FibrewiseCentralIsogenyReduction
import Langlands.GroupScheme.Reductive.RelativeCenterStatement
import Langlands.GroupScheme.Torus.MultiplicativeTypeFiniteSubgroupSpreadingStatement
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.AbelianScheme.TorsionFiniteEtale

/-! # Kernel geometry and assembly for the fibrewise central-isogeny criterion -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.FibrewiseCentralIsogenyAssembly

variable {S : Scheme.{u}} {G H Z : GroupScheme S}

/-- The canonical factor of a central full kernel through a supplied
scheme-theoretic centre. -/
def centralKernelFactor (f : G ⟶ H) (z : Z ⟶ G)
    (hz : IsSchemeTheoreticCenter z) (hc : IsCentral (kernelι f)) :
    kernel f ⟶ Z :=
  hz.isRepresentedBy.factorHom (kernelι f)
    ((isCentral_iff_range_le_center _).mp hc)

@[reassoc (attr := simp)]
theorem centralKernelFactor_comp (f : G ⟶ H) (z : Z ⟶ G)
    (hz : IsSchemeTheoreticCenter z) (hc : IsCentral (kernelι f)) :
    centralKernelFactor f z hz hc ≫ z = kernelι f :=
  hz.isRepresentedBy.factorHom_comp _ _

/-- With separated target, this factor is a closed immersion. -/
theorem centralKernelFactor_isClosedImmersion (f : G ⟶ H) (z : Z ⟶ G)
    (hz : IsSchemeTheoreticCenter z) (hc : IsCentral (kernelι f))
    [IsSeparated H.X.hom] :
    IsClosedImmersion (centralKernelFactor f z hz hc).hom.hom.left := by
  have : IsClosedImmersion z.hom.hom.left := hz.1
  have : IsClosedImmersion
      ((centralKernelFactor f z hz hc).hom.hom.left ≫ z.hom.hom.left) := by
    change IsClosedImmersion (centralKernelFactor f z hz hc ≫ z).hom.hom.left
    rw [centralKernelFactor_comp]
    infer_instance
  exact IsClosedImmersion.of_comp _ z.hom.hom.left

/-- A homomorphism between smooth group schemes is locally of finite
presentation over an arbitrary base. -/
theorem locallyOfFinitePresentation_hom (f : G ⟶ H)
    [Smooth G.X.hom] [Smooth H.X.hom] :
    LocallyOfFinitePresentation f.hom.hom.left := by
  have : LocallyOfFinitePresentation (f.hom.hom.left ≫ H.X.hom) := by
    rw [Over.w f.hom.hom]
    infer_instance
  exact Langlands.AlgebraicGeometry.locallyOfFinitePresentation_of_comp
    f.hom.hom.left H.X.hom

/-- The full kernel of a homomorphism between smooth group schemes is locally
of finite presentation, without a noetherian assumption on the base. -/
theorem locallyOfFinitePresentation_kernel (f : G ⟶ H)
    [Smooth G.X.hom] [Smooth H.X.hom] :
    LocallyOfFinitePresentation (kernel f).X.hom :=
  MorphismProperty.of_isPullback (kernel_isPullback_scheme f)
    (locallyOfFinitePresentation_hom f)

/-- Finiteness of the kernel after base change gives finiteness of the actual
base change of the kernel. -/
theorem finite_baseChanged_kernel {T : Scheme.{u}} (b : T ⟶ S) (f : G ⟶ H)
    (hf : IsFinite (kernel ((baseChange b).map f)).X.hom) :
    IsFinite ((baseChange b).obj (kernel f)).X.hom := by
  let e := kernelBaseChangeIso b f
  let := hf
  rw [← Over.w e.hom.hom.hom]
  infer_instance

/-- A central kernel with finite residue fibres is finite, provided the
relative-centre and multiplicative-type finite-subgroup spreading theorems. -/
theorem finite_kernel_of_central
    (hcenter : ReductiveRelativeCenterStatement.{u})
    (hspread : MultiplicativeTypeFiniteSubgroupSpreadingStatement.{u})
    (hG : IsReductive G) (hH : IsReductive H) (f : G ⟶ H)
    (hc : IsCentral (kernelι f))
    (hk : ∀ s : S,
      IsFinite (kernel ((baseChange (S.fromSpecResidueField s)).map f)).X.hom) :
    IsFinite (kernel f).X.hom := by
  let := hG.smooth
  let := hG.isAffineHom
  let := hH.smooth
  let := hH.isAffineHom
  have hfp := locallyOfFinitePresentation_kernel f
  have : IsAffineHom (kernel f).X.hom := by
    rw [← Over.w (kernelι f).hom.hom]
    infer_instance
  obtain ⟨Z, z, hz, hZm, -⟩ := hcenter S G hG
  have hzc := centralKernelFactor_isClosedImmersion f z hz hc
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := @IsFinite)
  intro s
  obtain ⟨U, hsU, n, hn, hkill, hfin⟩ :=
    (hspread S Z (kernel f) (centralKernelFactor f z hz hc) hZm hzc hfp
      inferInstance inferInstance s).1
      (finite_baseChanged_kernel (S.fromSpecResidueField s) f (hk s))
  refine ⟨U, hsU, ?_⟩
  have hpb := CategoryTheory.IsPullback.of_hasPullback (kernel f).X.hom U.ι
  rw [← hpb.isoIsPullback_inv_snd _ _
    (isPullback_morphismRestrict (kernel f).X.hom U).flip]
  exact (MorphismProperty.cancel_left_of_respectsIso @IsFinite _ _).mpr hfin

/-- After centrality is known, the two explicit structural theorems complete
the reverse implication of the fibrewise criterion. -/
theorem isCentralIsogeny_of_central_kernel
    (hcenter : ReductiveRelativeCenterStatement.{u})
    (hspread : MultiplicativeTypeFiniteSubgroupSpreadingStatement.{u})
    (hG : IsReductive G) (hH : IsReductive H) (f : G ⟶ H)
    (hs : Surjective f.hom.hom.left) (hc : IsCentral (kernelι f))
    (hk : ∀ s : S,
      IsFinite (kernel ((baseChange (S.fromSpecResidueField s)).map f)).X.hom) :
    IsCentralIsogeny f := by
  let := hG.smooth
  let := hH.smooth
  exact ⟨(FibrewiseCentralIsogenyReduction.isogeny_iff_finite_kernel hG hH f hs hk).mpr
      (finite_kernel_of_central hcenter hspread hG hH f hc hk),
    locallyOfFinitePresentation_hom f, hc⟩

/-- The exact published fibrewise criterion follows from the two named
structural statements and a global kernel-centrality theorem. -/
theorem criterion_of_kernelCentrality
    (hcenter : ReductiveRelativeCenterStatement.{u})
    (hspread : MultiplicativeTypeFiniteSubgroupSpreadingStatement.{u})
    (hcentral : ∀ (B : Scheme.{u}) (A C : GroupScheme B),
      IsReductive A → IsReductive C →
      ∀ (f : A ⟶ C), Surjective f.hom.hom.left →
        (∀ s : B,
          IsFinite (kernel ((baseChange (B.fromSpecResidueField s)).map f)).X.hom ∧
          IsCentral (kernelι ((baseChange (B.fromSpecResidueField s)).map f))) →
        IsCentral (kernelι f)) :
    ReductiveFibrewiseCentralIsogenyStatement.{u} := by
  intro B A C hA hC f hs
  constructor
  · exact fun hf s =>
      FibrewiseCentralIsogenyReduction.finite_central_kernel_fibres_of_isCentralIsogeny hf s
  · intro hf
    exact isCentralIsogeny_of_central_kernel hcenter hspread hA hC f hs
      (hcentral B A C hA hC f hs hf) (fun s => (hf s).1)

end Langlands.GroupScheme.FibrewiseCentralIsogenyAssembly
