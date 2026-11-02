import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainAlgebraPresheaf
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainAlgebraSheafExtension

/-! # The actual stored algebra maps to finite rational descent -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain

open CategoryTheory CategoryTheory.Limits Opposite

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (A : PresentedAffinoidAlgebra K)

/-- The actual bounded restrictions from a stored algebra satisfy the finite
rational intersection equations, hence map to the descent multiequalizer. -/
def algebraToExtension (U : Domain K A) :
    CommAlgCat.of K U.algebra ⟶ (algebraSheafExtension K A).obj.obj (op U) :=
  Multiequalizer.lift _ _
    (fun i => CommAlgCat.ofHom ((finiteRationalCoverData U).map i).restriction.toAlgHom)
    (by
      rintro ⟨⟨i, j⟩, t⟩
      ext a
      exact congrArg
        (fun f : Inclusion
            (((finiteRationalCoverData U).chart i).inter
              ((finiteRationalCoverData U).chart j)).toDomain U =>
          f.restriction a)
        ((RationalChart.finiteDomainHypercoverData U).w t))

@[reassoc (attr := simp)]
theorem algebraToExtension_projection (U : Domain K A)
    (i : Fin (finiteRationalCoverData U).size) :
    algebraToExtension K A U ≫ sectionProjection K A U i =
      CommAlgCat.ofHom ((finiteRationalCoverData U).map i).restriction.toAlgHom :=
  Multiequalizer.lift_ι _ _ _ _ _

variable {K A}

private theorem mapPreimage_eq_restriction {d e : RationalChart K A}
    (f : d.toDomain ⟶ e.toDomain) :
    Functor.IsDenseSubsite.mapPreimage (finiteDomainTopology K A)
        (RationalChart.toDomainFunctor K A) (RationalChart.algebraSheaf K A) f =
      CommAlgCat.ofHom f.restriction.toAlgHom := by
  exact Functor.IsDenseSubsite.mapPreimage_of_eq (finiteDomainTopology K A)
    (RationalChart.toDomainFunctor K A) (RationalChart.algebraSheaf K A) f
    (⟨f.restriction, f.comp_baseMap⟩ : RationalChart.Restriction d e)
    (Inclusion.ext rfl)

set_option backward.isDefEq.respectTransparency false in
/-- After any rational restriction, the finite-descent comparison is the
original actual bounded restriction from the stored algebra. -/
theorem algebraToExtension_restriction {U : Domain K A} {d : RationalChart K A}
    (f : d.toDomain ⟶ U) :
    algebraToExtension K A U ≫
        Functor.OneHypercoverDenseData.essSurj.restriction
          (RationalChart.finiteDomainHypercoverData (K := K) (A := A))
          (RationalChart.algebraSheaf K A) f =
      CommAlgCat.ofHom f.restriction.toAlgHom := by
  refine Presheaf.IsSheaf.hom_ext (RationalChart.algebraSheaf K A).property
    ⟨_, (RationalChart.finiteDomainHypercoverData U).sieve_mem f⟩ _ _ ?_
  rintro ⟨e, g, ⟨h⟩⟩
  dsimp
  rw [Category.assoc,
    Functor.OneHypercoverDenseData.essSurj.restriction_map
      (RationalChart.finiteDomainHypercoverData (K := K) (A := A))
      (RationalChart.algebraSheaf K A) f g h.q h.fac,
    ← Category.assoc]
  change (algebraToExtension K A U ≫ sectionProjection K A U h.i₀) ≫
      Functor.IsDenseSubsite.mapPreimage (finiteDomainTopology K A)
        (RationalChart.toDomainFunctor K A) (RationalChart.algebraSheaf K A) h.q =
    CommAlgCat.ofHom f.restriction.toAlgHom ≫
      CommAlgCat.ofHom g.restriction.toAlgHom
  rw [algebraToExtension_projection, mapPreimage_eq_restriction]
  ext a
  exact congrArg (fun q : Inclusion e.toDomain U => q.restriction a) h.fac

set_option backward.isDefEq.respectTransparency false in
/-- The actual comparison commutes with every stored bounded domain restriction. -/
@[reassoc]
theorem algebraToExtension_naturality {U V : Domain K A} (f : U ⟶ V) :
    CommAlgCat.ofHom f.restriction.toAlgHom ≫ algebraToExtension K A U =
      algebraToExtension K A V ≫ (algebraSheafExtension K A).obj.map f.op := by
  apply section_hom_ext
  intro i
  rw [Category.assoc, algebraToExtension_projection, Category.assoc]
  change _ = algebraToExtension K A V ≫
    (Functor.OneHypercoverDenseData.essSurj.presheafMap
        (RationalChart.finiteDomainHypercoverData (K := K) (A := A))
        (RationalChart.algebraSheaf K A) f ≫
      Functor.OneHypercoverDenseData.essSurj.presheafObjπ
        (RationalChart.finiteDomainHypercoverData (K := K) (A := A))
        (RationalChart.algebraSheaf K A) U i)
  rw [Functor.OneHypercoverDenseData.essSurj.presheafMap_π,
    algebraToExtension_restriction]
  rfl

variable (K A)

/-- The canonical algebra-presheaf map into finite rational descent. -/
def algebraToExtensionNat :
    algebraPresheaf K A ⟶ (algebraSheafExtension K A).obj where
  app U := algebraToExtension K A U.unop
  naturality _ _ f := algebraToExtension_naturality f.unop

set_option backward.isDefEq.respectTransparency false in
/-- On a rational image the comparison is the inverse of the constructed
section isomorphism with the original rational quotient algebra. -/
theorem algebraToExtension_rational (d : RationalChart K A) :
    algebraToExtension K A d.toDomain = (rationalSectionIso K A d).inv := by
  apply section_hom_ext
  intro i
  rw [algebraToExtension_projection]
  symm
  change Functor.OneHypercoverDenseData.essSurj.presheafObjObjIso.inv
        (RationalChart.finiteDomainHypercoverData (K := K) (A := A))
        (RationalChart.algebraSheaf K A) d ≫
      Functor.OneHypercoverDenseData.essSurj.presheafObjπ
        (RationalChart.finiteDomainHypercoverData (K := K) (A := A))
        (RationalChart.algebraSheaf K A) d.toDomain i = _
  exact (Functor.OneHypercoverDenseData.essSurj.presheafObjObjIso.inv_π
    (RationalChart.finiteDomainHypercoverData (K := K) (A := A))
    (RationalChart.algebraSheaf K A) d i).trans
      (mapPreimage_eq_restriction ((finiteRationalCoverData d.toDomain).map i))

set_option backward.isDefEq.respectTransparency false in
instance algebraToExtension_rational_isIso (d : RationalChart K A) :
    IsIso (algebraToExtension K A d.toDomain) := by
  rw [algebraToExtension_rational]
  exact (rationalSectionIso K A d).isIso_inv

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain
