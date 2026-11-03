import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.Dynamic.PositiveScaling

/-! # Independence of actual dynamic subgroups from lifts through a central kernel -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G H : GroupScheme S}

/-- Points with the same image through a homomorphism with central full kernel
induce the same conjugation on every point of the original group. -/
theorem conjugate_eq_of_comp_eq_of_central_kernel
    (q : G ⟶ H) (hq : IsCentral (kernelι q))
    {T : Over S} {a b : T ⟶ G.X}
    (hab : a ≫ q.hom.hom = b ≫ q.hom.hom) (x : T ⟶ G.X) :
    a * x * a⁻¹ = b * x * b⁻¹ := by
  have hk : (a⁻¹ * b) ≫ q.hom.hom = 1 := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, hab, inv_mul_cancel]
  have hc : Commute (a⁻¹ * b) x :=
    commute_of_mem_center ((isCentral_kernelι_iff q).mp hq T _ hk) x
  calc
    a * x * a⁻¹ = a * ((a⁻¹ * b) * x * (a⁻¹ * b)⁻¹) * a⁻¹ := by
      rw [hc.mul_inv_cancel]
    _ = b * x * b⁻¹ := by group

namespace Dynamic

variable (q : G ⟶ H) (hq : IsCentral (kernelι q))
    (χ ψ : (Gm S).toGrp ⟶ G) (hχψ : χ ≫ q = ψ ≫ q)

include hq hχψ

/-- Two actual lifts of the same cocharacter through a central full kernel
have identical conjugation orbit maps on every test scheme. -/
theorem orbit_eq_of_comp_eq_of_central_kernel {T : Over S} (g : T ⟶ G.X) :
    orbit χ g = orbit ψ g := by
  apply conjugate_eq_of_comp_eq_of_central_kernel q hq
  simpa only [Grp.comp_hom_hom, Category.assoc] using
    congrArg (fun f : (Gm S).toGrp ⟶ H => snd T (Gm S).X ≫ f.hom.hom) hχψ

/-- The same morphisms of the affine-line test extend either lifted orbit. -/
theorem isOrbitExtension_iff_of_comp_eq_of_central_kernel {T : Over S}
    (g : T ⟶ G.X) (e : T ⊗ AffineLine.scheme S ⟶ G.X) :
    IsOrbitExtension χ g e ↔ IsOrbitExtension ψ g e := by
  simp only [IsOrbitExtension, orbit_eq_of_comp_eq_of_central_kernel q hq χ ψ hχψ]

/-- Equal projected cocharacters have the same orbit limits in the original group. -/
theorem hasLimit_iff_of_comp_eq_of_central_kernel {T : Over S} (g l : T ⟶ G.X) :
    HasLimit χ g l ↔ HasLimit ψ g l := by
  simp only [HasLimit, isOrbitExtension_iff_of_comp_eq_of_central_kernel q hq χ ψ hχψ]

/-- The dynamic parabolic is independent of the actual lift through a central kernel. -/
theorem parabolic_eq_of_comp_eq_of_central_kernel :
    parabolic χ = parabolic ψ := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro g
  simp only [mem_parabolic,
    isOrbitExtension_iff_of_comp_eq_of_central_kernel q hq χ ψ hχψ]

/-- The dynamic centralizer is independent of the actual lift through a central kernel. -/
theorem centralizer_eq_of_comp_eq_of_central_kernel :
    centralizer χ = centralizer ψ := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro g
  simp only [mem_centralizer, orbit_eq_of_comp_eq_of_central_kernel q hq χ ψ hχψ]

/-- The dynamic identity-limit subgroup is independent of the actual lift through
a central kernel. -/
theorem unipotent_eq_of_comp_eq_of_central_kernel :
    unipotent χ = unipotent ψ := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro g
  simp only [mem_unipotent, hasLimit_iff_of_comp_eq_of_central_kernel q hq χ ψ hχψ]

end Dynamic

namespace Dynamic

variable {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)} [IsAffine G.X.left]
    (q : G ⟶ H) (hq : IsCentral (kernelι q))
    (χ ψ : (Gm (Spec R)).toGrp ⟶ G)

include hq in
/-- Positive powers of two projected cocharacters suffice to identify the actual
dynamic parabolics of their supplied lifts in the original affine group. -/
theorem parabolic_eq_of_positive_powers_comp_eq_of_central_kernel
    {m n : ℤ} (hm : 0 < m) (hn : 0 < n)
    (hχψ : (CommGroupScheme.groupHom (Gm.powerHom (Spec R) m) ≫ χ) ≫ q =
      (CommGroupScheme.groupHom (Gm.powerHom (Spec R) n) ≫ ψ) ≫ q) :
    parabolic χ = parabolic ψ := by
  calc
    parabolic χ =
        parabolic (CommGroupScheme.groupHom (Gm.powerHom (Spec R) m) ≫ χ) :=
      (parabolic_precomp_power χ hm).symm
    _ = parabolic (CommGroupScheme.groupHom (Gm.powerHom (Spec R) n) ≫ ψ) :=
      parabolic_eq_of_comp_eq_of_central_kernel q hq _ _ hχψ
    _ = parabolic ψ := parabolic_precomp_power ψ hn

namespace Affine

/-- The affine dynamic-parabolic representatives for two supplied lifts of the same
projected cocharacter are canonically isomorphic over the original ambient group. -/
def parabolicCentralKernelIso (hχψ : χ ≫ q = ψ ≫ q) :
    parabolicScheme χ ≅ parabolicScheme ψ :=
  (isRepresentedBy_parabolicHom χ).isoOfIsRepresentedBy
    (by
      rw [parabolic_eq_of_comp_eq_of_central_kernel q hq χ ψ hχψ]
      exact isRepresentedBy_parabolicHom ψ)

/-- The lift-independence isomorphism commutes with the original inclusions. -/
theorem parabolicCentralKernelIso_hom_comp (hχψ : χ ≫ q = ψ ≫ q) :
    (parabolicCentralKernelIso q hq χ ψ hχψ).hom ≫ parabolicHom ψ = parabolicHom χ :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

end Affine
end Dynamic
end Langlands.GroupScheme
