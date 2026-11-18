import Langlands.GroupScheme.SL2CentralExtension.Cell
import Langlands.GroupScheme.SL2CentralExtension.DComm
import Langlands.GroupScheme.SL2CentralExtension.Points
import Langlands.GroupScheme.SL2CentralExtension.Uniqueness
import Langlands.GroupScheme.SpecialLinearCentralExtensionSplitStatement

/-! # Proof that central extensions of `SL₂` split uniquely -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SL2CentralExtension

variable {S : Scheme.{u}}

/-- Composition with a homomorphism of group schemes, on points. -/
def postcomp {G H : GroupScheme S} (q : G ⟶ H) (T : Over S) : (T ⟶ G.X) →* (T ⟶ H.X) :=
  MonoidHom.mk' (fun x => x ≫ q.hom.hom) (fun a b => MonObj.mul_comp a b q.hom.hom)

/-- The point-level data of the central extension in the target statement. -/
def toExt {Z : CommGroupScheme S} (E : GroupScheme S) (z : Z.toGrp ⟶ E) (q : E ⟶ sl2 S)
    (hz : IsCentral z)
    (hker : ∀ (T : Over S) (x : T ⟶ E.X),
      x ≫ q.hom.hom = 1 ↔ x ∈ (SubgroupFunctor.range z).carrier T)
    (hlift : ∀ (T : Over S) (y : T ⟶ (sl2 S).X),
      ∃ 𝒰 : Scheme.Cover.{u}
          (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) T.left,
        ∀ i : 𝒰.I₀, ∃ x : Over.mk (𝒰.f i ≫ T.hom) ⟶ E.X,
          x ≫ q.hom.hom = (Over.homMk (𝒰.f i) rfl : Over.mk (𝒰.f i ≫ T.hom) ⟶ T) ≫ y) :
    Ext S where
  E := E
  Q T := (slEquiv T).toMonoidHom.comp (postcomp q T)
  Q_nat g e := by
    change slEquiv _ ((g ≫ e) ≫ q.hom.hom) = res g (slEquiv _ (e ≫ q.hom.hom))
    rw [Category.assoc, slEquiv_naturality]
  central {T} e e' he := by
    have he1 : e ≫ q.hom.hom = 1 := (slEquiv T).map_eq_one_iff.mp he
    obtain ⟨c, rfl⟩ := SubgroupFunctor.mem_range.mp ((hker T e).mp he1)
    exact commute_of_mem_center (hz T c) e'
  lift {T} m := by
    obtain ⟨𝒰, h𝒰⟩ := hlift T ((slEquiv T).symm m)
    refine (Loc.of_cover 𝒰).mono ?_
    rintro V g ⟨i, k, rfl⟩
    obtain ⟨x, hx⟩ := h𝒰 i
    refine ⟨k ≫ x, ?_⟩
    change slEquiv V ((k ≫ x) ≫ q.hom.hom) = res _ m
    rw [Category.assoc, hx, ← Category.assoc, slEquiv_naturality, MulEquiv.apply_symm_apply]
  sep {T} m m' h := by
    apply (slEquiv T).symm.injective
    apply Loc.ext
    refine h.mono fun V g hg => (slEquiv V).injective ?_
    rw [slEquiv_naturality, slEquiv_naturality, MulEquiv.apply_symm_apply,
      MulEquiv.apply_symm_apply]
    exact hg

namespace Ext

variable (X : Ext S)

/-- The splittings `sigma` on points are natural in the test scheme. -/
theorem sigma_slEquiv_nat (hD : X.DComm) {T T' : Over S} (a : T' ⟶ T) (x : T ⟶ (sl2 S).X) :
    ((X.sigma hD T').comp (slEquiv T').toMonoidHom) (a ≫ x) =
      a ≫ ((X.sigma hD T).comp (slEquiv T).toMonoidHom) x := by
  change X.sigma hD T' (slEquiv T' (a ≫ x)) = a ≫ X.sigma hD T (slEquiv T x)
  rw [slEquiv_naturality, X.sigma_res]

/-- The homomorphic section of `Q` built from the splittings `sigma` on points. -/
def section_ (hD : X.DComm) : sl2 S ⟶ X.E :=
  homOfPoints (fun T => (X.sigma hD T).comp (slEquiv T).toMonoidHom) (X.sigma_slEquiv_nat hD)

theorem Q_section (hD : X.DComm) {T : Over S} (x : T ⟶ (sl2 S).X) :
    X.Q T (x ≫ (X.section_ hD).hom.hom) = slEquiv T x := by
  have h := comp_homOfPoints (fun T => (X.sigma hD T).comp (slEquiv T).toMonoidHom)
    (X.sigma_slEquiv_nat hD) T x
  change X.Q T (x ≫ (homOfPoints _ (X.sigma_slEquiv_nat hD)).hom.hom) = _
  rw [h]
  exact X.Q_sigma hD (slEquiv T x)

end Ext

end Langlands.GroupScheme.SL2CentralExtension

namespace Langlands.GroupScheme

open SL2CentralExtension in
/-- **Central extensions of `SL₂` split uniquely** (Conrad, *Reductive group schemes*,
Proposition 4.3.1, due to Gabber): `SpecialLinearCentralExtensionSplitStatement` holds in every
universe. -/
theorem specialLinearCentralExtensionSplit : SpecialLinearCentralExtensionSplitStatement.{u} := by
  intro S
  dsimp only
  intro Z hZ E z q hmono hz hker hlift
  let X : Ext S := toExt E z q hz hker hlift
  have hi : ∀ ⦃T : Over S⦄ (e : T ⟶ X.E.X), X.Q T e = 1 → ∃ c : T ⟶ Z.X,
      c ≫ z.hom.hom = e := by
    intro T e he
    exact SubgroupFunctor.mem_range.mp
      ((hker T e).mp ((slEquiv T).map_eq_one_iff.mp he))
  have : IsSeparated Z.X.hom := hZ
  have hD : X.DComm := X.dComm_of_separated (Z := Z) z hi hmono
  obtain ⟨s, hs⟩ : ∃ s : sl2 S ⟶ E, ∀ (T : Over S) (x : T ⟶ (sl2 S).X),
      slEquiv T ((x ≫ s.hom.hom) ≫ q.hom.hom) = slEquiv T x :=
    ⟨X.section_ hD, fun T x => X.Q_section hD x⟩
  have hs' : s ≫ q = 𝟙 (sl2 S) := by
    apply hom_ext_points
    intro T x
    rw [Grp.comp_hom_hom, Grp.id_hom_hom, Category.comp_id, ← Category.assoc]
    exact (slEquiv T).injective (hs T x)
  exact ⟨s, hs', fun s' hs'' =>
    binarySpecialLinear_section_unique z q hz hker s' s hs'' hs'⟩

end Langlands.GroupScheme
