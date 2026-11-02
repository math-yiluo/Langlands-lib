import Langlands.GroupScheme.Dynamic.Basic
import Langlands.GroupScheme.InnerAutomorphism

/-! # Functoriality of dynamic subgroup functors in the group

For a homomorphism `f : H ⟶ G` of group schemes over `S`, this module defines the preimage
`SubgroupFunctor.comap f F` of a subgroup functor of `G`, and shows that the dynamic subgroup
functors of a cocharacter `χ` of `H` map into those of `χ ≫ f`:
`P_H(χ) ≤ f⁻¹ P_G(χ ≫ f)`, `Z_H(χ) ≤ f⁻¹ Z_G(χ ≫ f)` and `U_H(χ) ≤ f⁻¹ U_G(χ ≫ f)`.
The three inclusions are equalities when `f` is an isomorphism, so inner automorphisms transport
the dynamic subgroups of `χ` to those of the conjugate cocharacter; the centralizer inclusion is
an equality whenever `f` is a monomorphism of schemes.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}}

namespace SubgroupFunctor

variable {K H G : GroupScheme S}

/-- The preimage of a subgroup functor `F` of `G` under a homomorphism `f : H ⟶ G`: on every
test scheme, the points of `H` whose image under `f` lies in `F`. -/
def comap (f : H ⟶ G) (F : SubgroupFunctor G) : SubgroupFunctor H where
  carrier T := (F.carrier T).comap ((yonedaGrp.map f).app (op T)).hom
  comp_mem a x hx := by
    change (a ≫ x) ≫ f.hom.hom ∈ F.carrier _
    rw [Category.assoc]
    exact F.comp_mem a hx

theorem mem_comap {f : H ⟶ G} {F : SubgroupFunctor G} {T : Over S} {x : T ⟶ H.X} :
    x ∈ (F.comap f).carrier T ↔ x ≫ f.hom.hom ∈ F.carrier T :=
  Iff.rfl

@[simp] theorem comap_id (F : SubgroupFunctor G) : F.comap (𝟙 G) = F :=
  ext fun _ => Subgroup.ext fun x => by
    rw [mem_comap, Grp.id_hom_hom, Category.comp_id]

theorem comap_comp (f : K ⟶ H) (f' : H ⟶ G) (F : SubgroupFunctor G) :
    F.comap (f ≫ f') = (F.comap f').comap f :=
  ext fun _ => Subgroup.ext fun x => by
    rw [mem_comap, mem_comap, mem_comap, Grp.comp_hom_hom, Category.assoc]

theorem comap_mono {f : H ⟶ G} {F F' : SubgroupFunctor G} (h : F ≤ F') :
    F.comap f ≤ F'.comap f :=
  fun T _ hx => h T hx

@[simp] theorem comap_top (f : H ⟶ G) : (⊤ : SubgroupFunctor G).comap f = ⊤ :=
  ext fun _ => Subgroup.ext fun _ => iff_of_true (Subgroup.mem_top _) (Subgroup.mem_top _)

@[simp] theorem comap_inf (f : H ⟶ G) (F F' : SubgroupFunctor G) :
    (F ⊓ F').comap f = F.comap f ⊓ F'.comap f :=
  rfl

/-- The image of `f` lies in `F` exactly when the preimage of `F` is everything. -/
theorem range_le_iff_comap_eq_top {f : H ⟶ G} {F : SubgroupFunctor G} :
    range f ≤ F ↔ F.comap f = ⊤ := by
  constructor
  · intro h
    exact ext fun T => Subgroup.ext fun x =>
      iff_of_true (h T ⟨x, rfl⟩) (Subgroup.mem_top _)
  · rintro h T _ ⟨y, rfl⟩
    have hy : y ∈ (F.comap f).carrier T := by
      rw [h]
      exact Subgroup.mem_top _
    exact hy

/-- Preimages of normal subgroup functors are normal. -/
theorem IsNormal.comap {F : SubgroupFunctor G} (hF : F.IsNormal) (f : H ⟶ G) :
    (F.comap f).IsNormal := by
  intro T g x _ hx
  rw [mem_comap, MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp]
  exact hF T _ _ (Subgroup.mem_top _) hx

end SubgroupFunctor

namespace Dynamic

variable {H G : GroupScheme S} (χ : (Gm S).toGrp ⟶ H) (f : H ⟶ G)

/-- The orbit map of the image of a point under a homomorphism is the image of its orbit map. -/
theorem orbit_comp_hom {T : Over S} (g : T ⟶ H.X) :
    orbit (χ ≫ f) (g ≫ f.hom.hom) = orbit χ g ≫ f.hom.hom := by
  simp only [orbit, Grp.comp_hom_hom, MonObj.mul_comp, GrpObj.inv_comp, Category.assoc]

/-- Evaluation at zero commutes with composition. -/
theorem evalZero_comp {T Y Y' : Over S} (e : T ⊗ AffineLine.scheme S ⟶ Y) (k : Y ⟶ Y') :
    evalZero (e ≫ k) = evalZero e ≫ k :=
  (Category.assoc _ _ _).symm

/-- The image of an orbit extension under a homomorphism extends the image orbit. -/
theorem IsOrbitExtension.comp_hom {T : Over S} {g : T ⟶ H.X}
    {e : T ⊗ AffineLine.scheme S ⟶ H.X} (he : IsOrbitExtension χ g e) :
    IsOrbitExtension (χ ≫ f) (g ≫ f.hom.hom) (e ≫ f.hom.hom) := by
  rw [IsOrbitExtension, ← Category.assoc, he, orbit_comp_hom]

/-- Homomorphisms carry limits of orbits to limits of the image orbits. -/
theorem HasLimit.comp_hom {T : Over S} {g l : T ⟶ H.X} (hl : HasLimit χ g l) :
    HasLimit (χ ≫ f) (g ≫ f.hom.hom) (l ≫ f.hom.hom) := by
  obtain ⟨e, he, rfl⟩ := hl
  exact ⟨e ≫ f.hom.hom, he.comp_hom χ f, evalZero_comp e _⟩

/-- `P_H(χ) ≤ f⁻¹ P_G(χ ≫ f)`. -/
theorem parabolic_le_comap : parabolic χ ≤ (parabolic (χ ≫ f)).comap f := by
  rintro T g ⟨e, he⟩
  exact ⟨e ≫ f.hom.hom, he.comp_hom χ f⟩

/-- `Z_H(χ) ≤ f⁻¹ Z_G(χ ≫ f)`. -/
theorem centralizer_le_comap : centralizer χ ≤ (centralizer (χ ≫ f)).comap f := by
  intro T g hg
  rw [SubgroupFunctor.mem_comap, Dynamic.mem_centralizer, orbit_comp_hom,
    (mem_centralizer χ).mp hg, Category.assoc]

/-- `U_H(χ) ≤ f⁻¹ U_G(χ ≫ f)`. -/
theorem unipotent_le_comap : unipotent χ ≤ (unipotent (χ ≫ f)).comap f := by
  intro T g hg
  have h := HasLimit.comp_hom χ f ((mem_unipotent χ).mp hg)
  rw [MonObj.one_comp] at h
  exact h

/-- For a monomorphism `f`, `Z_H(χ) = f⁻¹ Z_G(χ ≫ f)`. -/
theorem centralizer_eq_comap_of_mono [Mono f.hom.hom] :
    centralizer χ = (centralizer (χ ≫ f)).comap f := by
  refine le_antisymm (centralizer_le_comap χ f) fun T g hg => ?_
  rw [SubgroupFunctor.mem_comap, Dynamic.mem_centralizer, orbit_comp_hom,
    ← Category.assoc] at hg
  exact (mem_centralizer χ).mpr ((cancel_mono _).mp hg)

section Iso

variable (e : H ≅ G)

theorem comp_hom_comp_inv : (χ ≫ e.hom) ≫ e.inv = χ := by
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem comp_hom_hom_comp_inv_hom {T : Over S} (g : T ⟶ H.X) :
    (g ≫ e.hom.hom.hom) ≫ e.inv.hom.hom = g := by
  rw [Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id, Grp.id_hom_hom, Category.comp_id]

/-- For an isomorphism `e`, `P_H(χ) = e⁻¹ P_G(χ ≫ e)`. -/
theorem parabolic_eq_comap_of_iso : parabolic χ = (parabolic (χ ≫ e.hom)).comap e.hom := by
  refine le_antisymm (parabolic_le_comap χ e.hom) fun T g hg => ?_
  have h : (g ≫ e.hom.hom.hom) ≫ e.inv.hom.hom ∈ (parabolic ((χ ≫ e.hom) ≫ e.inv)).carrier T :=
    parabolic_le_comap (χ ≫ e.hom) e.inv T hg
  rw [comp_hom_comp_inv, comp_hom_hom_comp_inv_hom] at h
  exact h

/-- For an isomorphism `e`, `Z_H(χ) = e⁻¹ Z_G(χ ≫ e)`. -/
theorem centralizer_eq_comap_of_iso :
    centralizer χ = (centralizer (χ ≫ e.hom)).comap e.hom := by
  refine le_antisymm (centralizer_le_comap χ e.hom) fun T g hg => ?_
  have h : (g ≫ e.hom.hom.hom) ≫ e.inv.hom.hom ∈ (centralizer ((χ ≫ e.hom) ≫ e.inv)).carrier T :=
    centralizer_le_comap (χ ≫ e.hom) e.inv T hg
  rw [comp_hom_comp_inv, comp_hom_hom_comp_inv_hom] at h
  exact h

/-- For an isomorphism `e`, `U_H(χ) = e⁻¹ U_G(χ ≫ e)`. -/
theorem unipotent_eq_comap_of_iso : unipotent χ = (unipotent (χ ≫ e.hom)).comap e.hom := by
  refine le_antisymm (unipotent_le_comap χ e.hom) fun T g hg => ?_
  have h : (g ≫ e.hom.hom.hom) ≫ e.inv.hom.hom ∈ (unipotent ((χ ≫ e.hom) ≫ e.inv)).carrier T :=
    unipotent_le_comap (χ ≫ e.hom) e.inv T hg
  rw [comp_hom_comp_inv, comp_hom_hom_comp_inv_hom] at h
  exact h

end Iso

section Conjugation

variable (χ : (Gm S).toGrp ⟶ G) (g : Over.mk (𝟙 S) ⟶ G.X)

/-- Conjugating by a base point `g` carries `P_G(χ)` onto `P_G(gχg⁻¹)`. -/
theorem mem_parabolic_conj {T : Over S} {x : T ⟶ G.X} :
    x ∈ (parabolic χ).carrier T ↔
      G.constantPoint g T * x * (G.constantPoint g T)⁻¹ ∈
        (parabolic (χ ≫ (G.innerIso g).hom)).carrier T := by
  conv_lhs => rw [parabolic_eq_comap_of_iso χ (G.innerIso g)]
  rw [SubgroupFunctor.mem_comap, comp_innerIso_hom]

/-- Conjugating by a base point `g` carries `Z_G(χ)` onto `Z_G(gχg⁻¹)`. -/
theorem mem_centralizer_conj {T : Over S} {x : T ⟶ G.X} :
    x ∈ (centralizer χ).carrier T ↔
      G.constantPoint g T * x * (G.constantPoint g T)⁻¹ ∈
        (centralizer (χ ≫ (G.innerIso g).hom)).carrier T := by
  conv_lhs => rw [centralizer_eq_comap_of_iso χ (G.innerIso g)]
  rw [SubgroupFunctor.mem_comap, comp_innerIso_hom]

/-- Conjugating by a base point `g` carries `U_G(χ)` onto `U_G(gχg⁻¹)`. -/
theorem mem_unipotent_conj {T : Over S} {x : T ⟶ G.X} :
    x ∈ (unipotent χ).carrier T ↔
      G.constantPoint g T * x * (G.constantPoint g T)⁻¹ ∈
        (unipotent (χ ≫ (G.innerIso g).hom)).carrier T := by
  conv_lhs => rw [unipotent_eq_comap_of_iso χ (G.innerIso g)]
  rw [SubgroupFunctor.mem_comap, comp_innerIso_hom]

end Conjugation

end Dynamic

end Langlands.GroupScheme
