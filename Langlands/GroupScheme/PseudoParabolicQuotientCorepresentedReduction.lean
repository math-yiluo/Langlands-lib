import Langlands.GroupScheme.PseudoParabolicQuotientDynamicCase
import Langlands.GroupScheme.Dynamic.FieldPointBasicOpen
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Reductive.GeneralLinear

/-! # Reduction of the dynamic case of CGP Proposition C.1.6 to corepresented groups

An affine group `G` over a field `k` is isomorphic to the corepresented group of its chosen
coordinate algebra, `AffineCoordinates.groupSchemeIso G`. Transporting the cocharacter, the
quotient map, pseudo-reductivity and the fibre condition along this isomorphism reduces
`DynamicParabolicQuotientDVRLifting k` to the same statement for corepresented groups, phrased
with the spectra `algOver k A` and the maps `algOverHom φ`. The module also records that a
pseudo-reductive corepresented group has a finite type coordinate algebra.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

namespace Corepresented

variable {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} (CommRingCat.of k)} {e : (F ⋙ forget GrpCat).CorepresentableBy B}

/-- A corepresented group whose structure morphism is locally of finite type has a finite type
coordinate algebra. -/
theorem algebraFiniteType_of_locallyOfFiniteType
    [LocallyOfFiniteType (groupScheme F e).X.hom] : Algebra.FiniteType k B := by
  have h : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k B))) :=
    inferInstanceAs (LocallyOfFiniteType (groupScheme F e).X.hom)
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h
  exact RingHom.finiteType_algebraMap.mp h

/-- A pseudo-reductive corepresented group has a finite type coordinate algebra. -/
theorem algebraFiniteType_of_isPseudoReductive (hG : IsPseudoReductive (groupScheme F e)) :
    Algebra.FiniteType k B := by
  have := hG.smooth
  exact algebraFiniteType_of_locallyOfFiniteType (e := e)

end Corepresented

open Corepresented in
/-- The dynamic case of C.1.6 for corepresented groups, with points over `Frac R` and `R` given
as morphisms from `algOver k (Frac R)` and `algOver k R`. -/
def CorepresentedDynamicParabolicQuotientDVRLifting (k : Type u) [Field k] : Prop :=
  ∀ (F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}) (B : CommAlgCat.{u} (CommRingCat.of k))
    (e : (F ⋙ forget GrpCat).CorepresentableBy B)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ groupScheme F e)
    (Q : Over (Spec (CommRingCat.of k))) (q : (groupScheme F e).X ⟶ Q),
    IsPseudoReductive (groupScheme F e) → Smooth q.left → Surjective q.left →
    QuasiCompact q.left →
    (∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ (groupScheme F e).X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (Dynamic.parabolic χ).carrier T) →
    ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra k R],
      Algebra.IsGeometricallyReduced k (IsLocalRing.ResidueField R) →
      ∀ x : algOver k (FractionRing R) ⟶ Q, ∃ xR : algOver k R ⟶ Q,
        algOverHom (IsScalarTower.toAlgHom k R (FractionRing R)) ≫ xR = x

/-- The canonical generic-point map is `algOverHom` of the inclusion `R → Frac R`. -/
theorem PseudoComplete.genericPoint_eq_algOverHom (R : Type u) [CommRing R] [IsDomain R]
    [Algebra k R] :
    (PseudoComplete.genericPoint (k := k) R :
        Corepresented.algOver k (FractionRing R) ⟶ Corepresented.algOver k R) =
      Corepresented.algOverHom (IsScalarTower.toAlgHom k R (FractionRing R)) :=
  Over.OverMorphism.ext rfl

/-- **Reduction to corepresented groups.** The dynamic case of C.1.6 over `k` follows from its
corepresented version, by transport along `AffineCoordinates.groupSchemeIso`. -/
theorem dynamicParabolicQuotientDVRLifting_of_corepresented
    (hcore : CorepresentedDynamicParabolicQuotientDVRLifting k) :
    DynamicParabolicQuotientDVRLifting k := by
  intro G χ Q q hG hsm hsurj hqc hfib R _ _ _ _ hres x
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let e := AffineCoordinates.groupSchemeIso G
  let χ₀ := Dynamic.Affine.cocharacter χ
  let q₀ := e.hom.hom.hom ≫ q
  have : IsIso e.hom.hom.hom.left := isIso_left_of_iso e
  have hχ : χ₀ ≫ e.hom = χ := by
    simp only [χ₀, Dynamic.Affine.cocharacter, e, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  have hfib₀ : ∀ (T : Over (Spec (CommRingCat.of k)))
      (g h : T ⟶ (Corepresented.groupScheme (AffineCoordinates.functor G)
        (AffineCoordinates.corepresentation G)).X),
      g ≫ q₀ = h ≫ q₀ ↔ g⁻¹ * h ∈ (Dynamic.parabolic χ₀).carrier T := by
    intro T g h
    rw [Dynamic.parabolic_eq_comap_of_iso χ₀ e, hχ, SubgroupFunctor.mem_comap,
      MonObj.mul_comp, GrpObj.inv_comp, ← hfib]
    simp only [q₀, Category.assoc]
  have hsm₀ : Smooth q₀.left := by
    change Smooth (e.hom.hom.hom.left ≫ q.left)
    infer_instance
  have hsurj₀ : Surjective q₀.left := by
    change Surjective (e.hom.hom.hom.left ≫ q.left)
    infer_instance
  have hqc₀ : QuasiCompact q₀.left := by
    change QuasiCompact (e.hom.hom.hom.left ≫ q.left)
    infer_instance
  obtain ⟨xR, hxR⟩ := hcore _ _ _ χ₀ Q q₀ (IsPseudoReductive.of_iso e hG) hsm₀ hsurj₀ hqc₀ hfib₀
    R hres x
  exact ⟨xR, (PseudoComplete.genericPoint_eq_algOverHom (k := k) R ▸ hxR :)⟩

end Langlands.GroupScheme
