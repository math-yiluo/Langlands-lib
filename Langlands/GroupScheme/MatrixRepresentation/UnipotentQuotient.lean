import Langlands.GroupScheme.MatrixRepresentation.UnipotentKernel
import Langlands.GroupScheme.ActionDescent

/-! # Faithful representations of supplied fpqc unipotent quotients -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace FpqcHomDescent

variable {S : Scheme.{u}} {G Q L : GroupScheme S}

/-- A factor of an fpqc group quotient is a monomorphism if no further kernel
points are killed on the source. -/
theorem mono_of_kernel_range_le (q : G ⟶ Q) (f : G ⟶ L) (d : Q ⟶ L)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [QuasiCompact q.hom.hom.left]
    (hfac : q ≫ d = f)
    (hk : SubgroupFunctor.range (kernelι f) ≤ SubgroupFunctor.range (kernelι q)) :
    Mono d.hom.hom := by
  have htriv (T : Over S) (x : T ⟶ Q.X) (hx : x ≫ d.hom.hom = 1) :
      x = 1 := by
    apply AutomorphicAction.hom_ext_of_local_quotient_lift q x
    intro V b g hbg
    have hgf : g ≫ f.hom.hom = 1 := by
      rw [← hfac, Grp.comp_hom_hom, ← Category.assoc, ← hbg,
        Category.assoc, hx]
      exact MonObj.comp_one b
    have hgq : g ≫ q.hom.hom = 1 :=
      (mem_range_kernelι_iff q g).mp (hk V ((mem_range_kernelι_iff f g).mpr hgf))
    rw [hbg, hgq, MonObj.comp_one]
  constructor
  intro T x y hxy
  have hinj : Function.Injective ((yonedaGrp.map d).app (op T)).hom := by
    apply (injective_iff_map_eq_one _).mpr
    intro z hz
    exact htriv T z hz
  exact hinj hxy

end FpqcHomDescent

namespace MatrixRepresentation

variable {k : Type u} [Field k]
  {G H Q : GroupScheme (Spec (CommRingCat.of k))}

namespace KernelCoordinates

variable {i : H ⟶ G} (c : KernelCoordinates i) (q : G ⟶ Q)
  (hq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range i)

include hq

/-- A representation with the prescribed kernel kills the quotient kernel. -/
theorem kernel_comp_eq_zero : kernelι q ≫ c.representation = 0 := by
  apply Grp.hom_ext
  change (kernelι q).hom.hom ≫ c.representation.hom.hom = 1
  apply (mem_range_kernelι_iff c.representation _).mp
  rw [c.kernel_eq, ← hq]
  exact SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩

variable [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
  [QuasiCompact q.hom.hom.left]

/-- The actual representation descended to the supplied fpqc quotient. -/
def descend : MatrixRepresentation Q (Fin c.dimension) :=
  FpqcHomDescent.hom q c.representation (c.kernel_comp_eq_zero q hq)

/-- Pullback along the quotient recovers the exact-kernel representation. -/
@[reassoc]
theorem descend_fac : q ≫ c.descend q hq = c.representation :=
  FpqcHomDescent.fac _ _ _

/-- The descended representation is faithful on every relative scheme test. -/
theorem descend_mono : Mono (c.descend q hq).hom.hom :=
  FpqcHomDescent.mono_of_kernel_range_le q c.representation (c.descend q hq)
    (c.descend_fac q hq) (by rw [c.kernel_eq, hq])

end KernelCoordinates

/-- An fpqc quotient of an affine finite-type group by a closed unipotent normal
subgroup has a faithful actual finite-dimensional representation over its field. -/
theorem exists_faithful_of_unipotent_kernel
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (i : H ⟶ G) (hc : IsClosedSubgroup i) (hH : IsUnipotent H)
    (hN : (SubgroupFunctor.range i).IsNormal)
    (q : G ⟶ Q) [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [QuasiCompact q.hom.hom.left]
    (hq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range i) :
    ∃ (n : ℕ) (ρ : MatrixRepresentation Q (Fin n)), Mono ρ.hom.hom := by
  let c := unipotentKernelCoordinates i hc hH hN
  exact ⟨c.dimension, c.descend q hq, c.descend_mono q hq⟩

end MatrixRepresentation

end Langlands.GroupScheme
