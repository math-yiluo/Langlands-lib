import Langlands.GroupScheme.Rational.QuasiSplitPinningOrbitPairs
import Langlands.GroupScheme.Rational.ClassFunctionsQuotientDescent
import Langlands.GroupScheme.Rational.SplitSteinbergImmersionProof
import Langlands.GroupScheme.Rational.SplitSteinbergQuotientStatement
import Langlands.GroupScheme.SimplyConnected.SemisimpleFieldExtensionProof

/-! # Descended Steinberg sections for orthogonal simple-root orbits -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace Langlands.GroupScheme

namespace DescendedClosedImmersion

section Schemes

variable {X Y Z : Scheme.{u}} (p : X ⟶ Y) (J : Y.IdealSheafData) (m : Z ⟶ X)
    (h : m.ker = J.comap p)

/-- The factorization of the closed immersion through the descended subscheme. -/
def lift : Z ⟶ J.subscheme :=
  IsClosedImmersion.lift J.subschemeι (m ≫ p) (by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact (ideal_comap_le_ker_iff J p m).mp h.ge)

@[reassoc (attr := simp)]
theorem lift_subschemeι : lift p J m h ≫ J.subschemeι = m ≫ p :=
  IsClosedImmersion.lift_fac _ _ _

/-- The closed immersion is the base change of the descended subscheme. -/
theorem isPullback [IsClosedImmersion m] : IsPullback m (lift p J m h) p J.subschemeι :=
  isPullback_of_isClosedImmersion m J.subschemeι (lift p J m h) p
    (lift_subschemeι p J m h).symm (by rw [Scheme.IdealSheafData.ker_subschemeι, h])

end Schemes

section Over

variable {S S' : Scheme.{u}} (b : S' ⟶ S) (X : Over S) (J : X.left.IdealSheafData)

/-- The closed subscheme cut out by an ideal of the underlying scheme, over the base. -/
def subOver : Over S := Over.mk (J.subschemeι ≫ X.hom)

/-- Its inclusion. -/
def subOverι : subOver X J ⟶ X := Over.homMk J.subschemeι rfl

variable {X J} {Z : Over S'} (m : Z ⟶ (Over.pullback b).obj X) [IsClosedImmersion m.left]
    (h : m.left.ker = J.comap (pullback.fst X.hom b))

/-- The descended pasted square. -/
theorem isPullback_pasted :
    IsPullback (lift (pullback.fst X.hom b) J m.left h) Z.hom (J.subschemeι ≫ X.hom) b := by
  have h1 := (isPullback (pullback.fst X.hom b) J m.left h).flip
  have h2 := IsPullback.of_hasPullback X.hom b
  have h3 := h1.paste_vert h2
  have hw : m.left ≫ pullback.snd X.hom b = Z.hom := Over.w m
  rwa [hw] at h3

/-- The source of the closed immersion is the base change of the descended subscheme. -/
def overIso : Z ≅ (Over.pullback b).obj (subOver X J) :=
  Over.isoMk (isPullback_pasted b m h).isoPullback (by
    simp [subOver])

theorem overIso_hom_comp :
    (overIso b m h).hom ≫ (Over.pullback b).map (subOverι X J) = m := by
  ext1
  apply pullback.hom_ext
  · simp [overIso, subOverι, subOver]
  · simp [overIso, subOverι, subOver]
    exact (Over.w m).symm

/-- The base change of the descended inclusion is the given closed immersion. -/
@[reassoc]
theorem pullback_map_subOverι :
    (Over.pullback b).map (subOverι X J) = (overIso b m h).inv ≫ m := by
  rw [Iso.eq_inv_comp, overIso_hom_comp]

end Over

end DescendedClosedImmersion

namespace GaloisCompatiblePinningData

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance quasiSplitOrdinarySectionIsAffineHom : IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

variable (D : GaloisCompatiblePinningData k K G)

/-- The canonical Steinberg product of the pinning in simple-root orbit order. -/
abbrev orbitProduct :=
  SplitPinning.steinbergProduct (D.pinning.simpleOrbitOrdering D.action) D.rootMaps
    (SplitPinning.canonicalSimpleReflectionRepresentatives D.rootMaps)

/-- For a semisimple group the orbit-ordered product is a closed immersion. -/
theorem orbitProduct_isClosedImmersion (hG : IsSemisimple G) :
    IsClosedImmersion D.orbitProduct.left :=
  splitSteinbergImmersion K _ D.pinning (isSemisimpleFieldExtension k K G hG) _ _ _ _

variable [IsGalois k K] (horth : D.pinning.OrthogonalSimpleOrbits D.action)

/-- The descended Steinberg section as a scheme over the ground field: the closed
subscheme cut out by the descended ideal of the orbit-ordered Steinberg product. -/
def sectionScheme : Over (Spec (CommRingCat.of k)) :=
  DescendedClosedImmersion.subOver G.X (D.definingIdealDescent horth).ideal

/-- Its inclusion into the group. -/
def sectionι : D.sectionScheme horth ⟶ G.X :=
  DescendedClosedImmersion.subOverι G.X (D.definingIdealDescent horth).ideal

theorem sectionι_eq :
    D.sectionι horth =
      DescendedClosedImmersion.subOverι G.X (D.definingIdealDescent horth).ideal :=
  rfl

/-- The scalar extension of the descended inclusion, followed by the split quotient map. -/
theorem quotientComposite_sectionι :
    ClassFunctions.BaseChange.quotientComposite k K G (D.sectionι horth) =
      (Over.pullback (algebraBaseMap k K)).map (D.sectionι horth) ≫
        ClassFunctions.rho ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) :=
  rfl

/-- If the split orbit-ordered product is a closed immersion whose composite with the
canonical quotient map is an isomorphism, so is the descended section over `k`. -/
theorem isIso_sectionι_rho (himm : IsClosedImmersion D.orbitProduct.left)
    (hq : IsIso (D.orbitProduct ≫
      ClassFunctions.rho ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))) :
    IsIso (D.sectionι horth ≫ ClassFunctions.rho G) := by
  rw [← ClassFunctions.BaseChange.isIso_quotientComposite_iff k K G,
    D.quotientComposite_sectionι horth, D.sectionι_eq horth,
    DescendedClosedImmersion.pullback_map_subOverι_assoc (algebraBaseMap k K) D.orbitProduct
      (D.definingIdealDescent horth).eq_comap]
  infer_instance

include horth in
/-- Every rational point of the canonical quotient lifts to a rational point of the group. -/
theorem exists_rationalLift (himm : IsClosedImmersion D.orbitProduct.left)
    (hq : IsIso (D.orbitProduct ≫
      ClassFunctions.rho ((GroupScheme.baseChange (algebraBaseMap k K)).obj G)))
    (v : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ ClassFunctions.quotient G) :
    ∃ x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X, x ≫ ClassFunctions.rho G = v := by
  have := D.isIso_sectionι_rho horth himm hq
  refine ⟨v ≫ inv (D.sectionι horth ≫ ClassFunctions.rho G) ≫ D.sectionι horth, ?_⟩
  rw [Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

include horth in
/-- Rational lifting for simply connected groups, given the split quotient statement
and simple connectedness of the split base change. -/
theorem exists_rationalLift_of_isSimplyConnected
    (hsq : SplitSteinbergQuotientStatement.{u}) (hG : IsSimplyConnected G)
    (hGK : IsSimplyConnected ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))
    (v : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ ClassFunctions.quotient G) :
    ∃ x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X, x ≫ ClassFunctions.rho G = v :=
  D.exists_rationalLift horth (D.orbitProduct_isClosedImmersion hG.isSemisimple)
    (hsq K _ D.pinning hGK _ _ _ _) v

end GaloisCompatiblePinningData

namespace PairingCompatiblePinningData

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (D : PairingCompatiblePinningData k K G)

/-- For a simply connected group, either the simple-root orbits are orthogonal and every
rational point of the canonical quotient lifts to a rational point of the group, or some
orbit contains an `A₂` pair swapped by the moving Galois element. -/
theorem rationalLift_or_exists_pair
    (hsq : SplitSteinbergQuotientStatement.{u})
    (hsc : IsSimplyConnectedFieldExtensionStatement.{u}) (hG : IsSimplyConnected G) :
    (D.pinning.OrthogonalSimpleOrbits D.action ∧
      ∀ v : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ ClassFunctions.quotient G,
        ∃ x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X, x ≫ ClassFunctions.rho G = v) ∨
      ∃ (σ : K ≃ₐ[k] K) (a : D.pinning.base.support), D.action σ a ≠ a ∧
        D.pinning.rootDatum.pairing a (D.action σ a) = -1 ∧
        D.pinning.rootDatum.pairing (D.action σ a) a = -1 ∧
        D.action σ (D.action σ a) = a := by
  rcases D.orthogonalSimpleOrbits_or_exists_pair with horth | hpair
  · exact Or.inl ⟨horth, D.toGaloisCompatiblePinningData.exists_rationalLift_of_isSimplyConnected
      horth hsq hG (hsc k K G hG)⟩
  · exact Or.inr hpair

end PairingCompatiblePinningData

section QuasiSplit

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom]

/-- A simply connected quasi-split group has pairing-compatible pinning data over a finite
Galois extension for which either every rational point of the canonical quotient lifts to a
rational point of the group, or some Galois element swaps an `A₂` pair of simple roots.
Conditional on the parabolic dynamic statement, the existence of root data of split
reductive groups, the split Steinberg quotient statement and the field-extension
compatibility of simple connectedness. -/
theorem IsQuasiSplit.exists_pairingCompatiblePinningData_rationalLift_or_exists_pair
    (hPD : ParabolicDynamicStatement.{u}) (hRDE : RootDatumExistenceStatement.{u})
    (hsq : SplitSteinbergQuotientStatement.{u})
    (hsc : IsSimplyConnectedFieldExtensionStatement.{u})
    (hG : IsSimplyConnected G) (hq : IsQuasiSplit G) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K), FiniteDimensional k K ∧ IsGalois k K ∧
      ∃ D : PairingCompatiblePinningData k K G,
        (D.pinning.OrthogonalSimpleOrbits D.action ∧
          ∀ v : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ ClassFunctions.quotient G,
            ∃ x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X,
              x ≫ ClassFunctions.rho G = v) ∨
          ∃ (σ : K ≃ₐ[k] K) (a : D.pinning.base.support), D.action σ a ≠ a ∧
            D.pinning.rootDatum.pairing a (D.action σ a) = -1 ∧
            D.pinning.rootDatum.pairing (D.action σ a) a = -1 ∧
            D.action σ (D.action σ a) = a := by
  obtain ⟨K, hK, hAK, hfin, hgal, ⟨D⟩⟩ := hq.exists_pairingCompatiblePinningData hPD hRDE
  exact ⟨K, hK, hAK, hfin, hgal, D, D.rationalLift_or_exists_pair hsq hsc hG⟩

end QuasiSplit

end Langlands.GroupScheme
