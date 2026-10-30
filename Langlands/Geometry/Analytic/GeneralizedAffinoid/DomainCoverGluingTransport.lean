import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainCoverBaseTransport
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainCoverDescent

/-! # Continuous finite-cover gluing under bounded base equivalences -/

noncomputable section

universe u v w

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteCover

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {A B : PresentedAffinoidAlgebra K} {V : Domain K A}
variable (c : FiniteCover V)
variable {Y : Type v} [TopologicalSpace Y]

/-- Transport a family through the component locus homeomorphisms induced
by the actual bounded equivalence of ambient algebras. -/
def transportBaseFamily (e : BoundedAlgEquiv K A B)
    (g : ∀ i : Fin c.size, C((c.obj i).locus, Y)) :
    ∀ i : Fin (c.transportBase e).size, C(((c.transportBase e).obj i).locus, Y) :=
  fun i => (g i).comp
    (Domain.transportBaseLocusHomeomorph e (c.obj i) :
      C((Domain.transportBase e (c.obj i)).locus, (c.obj i).locus))

/-- The inverse family uses the actual inverse component homeomorphisms,
without changing or choosing component indices. -/
def transportBaseFamilyInverse (e : BoundedAlgEquiv K A B)
    (g : ∀ i : Fin (c.transportBase e).size,
      C(((c.transportBase e).obj i).locus, Y)) :
    ∀ i : Fin c.size, C((c.obj i).locus, Y) :=
  fun i => (g i).comp
    ((Domain.transportBaseLocusHomeomorph e (c.obj i)).symm :
      C((c.obj i).locus, (Domain.transportBase e (c.obj i)).locus))

theorem compatible_transportBaseFamily (e : BoundedAlgEquiv K A B)
    (g : ∀ i : Fin c.size, C((c.obj i).locus, Y)) (hg : c.Compatible g) :
    (c.transportBase e).Compatible (c.transportBaseFamily e g) := by
  intro i j x y h
  exact hg i j _ _ (congrArg e.spectrumHomeomorph h)

theorem compatible_transportBaseFamilyInverse (e : BoundedAlgEquiv K A B)
    (g : ∀ i : Fin (c.transportBase e).size,
      C(((c.transportBase e).obj i).locus, Y))
    (hg : (c.transportBase e).Compatible g) :
    c.Compatible (c.transportBaseFamilyInverse e g) := by
  intro i j x y h
  exact hg i j _ _ (congrArg e.spectrumHomeomorph.symm h)

@[simp] theorem transportBaseFamilyInverse_transportBaseFamily
    (e : BoundedAlgEquiv K A B)
    (g : ∀ i : Fin c.size, C((c.obj i).locus, Y)) :
    c.transportBaseFamilyInverse e (c.transportBaseFamily e g) = g := by
  funext i
  apply ContinuousMap.ext
  intro x
  change g i ((Domain.transportBaseLocusHomeomorph e (c.obj i))
    ((Domain.transportBaseLocusHomeomorph e (c.obj i)).symm x)) = g i x
  rw [Homeomorph.apply_symm_apply]

@[simp] theorem transportBaseFamily_transportBaseFamilyInverse
    (e : BoundedAlgEquiv K A B)
    (g : ∀ i : Fin (c.transportBase e).size,
      C(((c.transportBase e).obj i).locus, Y)) :
    c.transportBaseFamily e (c.transportBaseFamilyInverse e g) = g := by
  funext i
  apply ContinuousMap.ext
  intro x
  change g i ((Domain.transportBaseLocusHomeomorph e (c.obj i)).symm
    ((Domain.transportBaseLocusHomeomorph e (c.obj i)) x)) = g i x
  exact congrArg (g i)
    ((Domain.transportBaseLocusHomeomorph e (c.obj i)).symm_apply_apply x)

/-- Compatible continuous families are transported by a constructed
equivalence with the actual inverse component homeomorphisms. -/
def transportBaseFamilyEquiv (e : BoundedAlgEquiv K A B) :
    CompatibleFamily c Y ≃ CompatibleFamily (c.transportBase e) Y where
  toFun g := ⟨c.transportBaseFamily e g.val,
    c.compatible_transportBaseFamily e g.val g.property⟩
  invFun g := ⟨c.transportBaseFamilyInverse e g.val,
    c.compatible_transportBaseFamilyInverse e g.val g.property⟩
  left_inv g := Subtype.ext (c.transportBaseFamilyInverse_transportBaseFamily e g.val)
  right_inv g := Subtype.ext (c.transportBaseFamily_transportBaseFamilyInverse e g.val)

@[simp] theorem transportBaseFamilyEquiv_apply (e : BoundedAlgEquiv K A B)
    (g : CompatibleFamily c Y) (i : Fin c.size)
    (x : ((c.transportBase e).obj i).locus) :
    (c.transportBaseFamilyEquiv e g).val i x =
      g.val i (Domain.transportBaseLocusHomeomorph e (c.obj i) x) := rfl

/-- Restriction of a transported global map is componentwise transport
of its original restrictions. -/
theorem transportBaseFamily_restrict (e : BoundedAlgEquiv K A B)
    (f : C(V.locus, Y)) :
    c.transportBaseFamily e (c.restrict f) =
      (c.transportBase e).restrict
        (f.comp (Domain.transportBaseLocusHomeomorph e V :
          C((Domain.transportBase e V).locus, V.locus))) := by
  funext i
  apply ContinuousMap.ext
  intro x
  exact congrArg f
    (Domain.transportBaseLocusHomeomorph_naturality e (c.map i) x).symm

/-- The compatible-family equivalence commutes with the concrete gluing
equivalences on global continuous maps. -/
theorem transportBaseFamilyEquiv_gluingEquiv (e : BoundedAlgEquiv K A B)
    (f : C(V.locus, Y)) :
    c.transportBaseFamilyEquiv e (c.gluingEquiv f) =
      (c.transportBase e).gluingEquiv
        (f.comp (Domain.transportBaseLocusHomeomorph e V :
          C((Domain.transportBase e V).locus, V.locus))) := by
  apply Subtype.ext
  exact c.transportBaseFamily_restrict e f

/-- Gluing a transported compatible family is the original glued map
composed with the actual target locus homeomorphism. -/
theorem glue_transportBaseFamily (e : BoundedAlgEquiv K A B)
    (g : ∀ i : Fin c.size, C((c.obj i).locus, Y)) (hg : c.Compatible g) :
    (c.transportBase e).glue (c.transportBaseFamily e g)
        (c.compatible_transportBaseFamily e g hg) =
      (c.glue g hg).comp (Domain.transportBaseLocusHomeomorph e V :
        C((Domain.transportBase e V).locus, V.locus)) := by
  apply ((c.transportBase e).glue_unique _ _ _ ?_).symm
  intro i
  rw [← c.transportBaseFamily_restrict e (c.glue g hg)]
  change (c.restrict (c.glue g hg) i).comp
      (Domain.transportBaseLocusHomeomorph e (c.obj i) :
        C((Domain.transportBase e (c.obj i)).locus, (c.obj i).locus)) =
    (g i).comp (Domain.transportBaseLocusHomeomorph e (c.obj i) :
      C((Domain.transportBase e (c.obj i)).locus, (c.obj i).locus))
  exact congrArg
    (fun f : C((c.obj i).locus, Y) => f.comp
      (Domain.transportBaseLocusHomeomorph e (c.obj i) :
        C((Domain.transportBase e (c.obj i)).locus, (c.obj i).locus)))
    (c.restrict_glue g hg i)

/-- The disjoint union of actual component spectra is unchanged, and its
assembled continuous map agrees exactly with the original assembly. -/
theorem transportBaseFamily_spectrumFamilyMap (e : BoundedAlgEquiv K A B)
    (g : ∀ i : Fin c.size, C((c.obj i).locus, Y)) :
    (c.transportBase e).spectrumFamilyMap (c.transportBaseFamily e g) =
      c.spectrumFamilyMap g := by
  apply ContinuousMap.ext
  intro x
  change g x.1 (Domain.transportBaseLocusHomeomorph e (c.obj x.1)
    ((Domain.transportBase e (c.obj x.1)).spectrumToLocus x.2)) =
      g x.1 ((c.obj x.1).spectrumToLocus x.2)
  exact congrArg (g x.1)
    (Domain.transportBase_spectrumToLocus e (c.obj x.1) x.2)

variable {Z : Type w} [TopologicalSpace Z]

/-- Transport commutes with every continuous map of target spaces. -/
theorem transportBaseFamily_postcomp (e : BoundedAlgEquiv K A B)
    (g : ∀ i : Fin c.size, C((c.obj i).locus, Y)) (p : C(Y, Z)) :
    c.transportBaseFamily e (fun i => p.comp (g i)) =
      fun i => p.comp (c.transportBaseFamily e g i) := by
  funext i
  apply ContinuousMap.ext
  intro x
  rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteCover
