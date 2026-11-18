import Langlands.GroupScheme.Torus.DiagonalizableIsoLift

/-! # Diagonalizable homomorphisms and the topology of the base -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeMultiplicativeType

variable {X Y : Scheme.{u}}
  {M N : Type u} [AddCommGroup M] [AddCommGroup N]

/-- The open locus on which an actual split homomorphism is a fixed character map. -/
def homLocus (f : diagonalizable X M ⟶ diagonalizable X N) (g : N →+ M) : X.Opens :=
  sSup {V : X.Opens | dpull V.ι f = diagonalizableMap V g}

theorem mem_homLocus {f : diagonalizable X M ⟶ diagonalizable X N}
    {g : N →+ M} {x : X} :
    x ∈ homLocus f g ↔
      ∃ V : X.Opens, x ∈ V ∧ dpull V.ι f = diagonalizableMap V g := by
  rw [homLocus, TopologicalSpace.Opens.mem_sSup]
  exact ⟨fun ⟨V, hV, hx⟩ => ⟨V, hx, hV⟩, fun ⟨V, hx, hV⟩ => ⟨V, hV, hx⟩⟩

theorem homLocus_disjoint (f : diagonalizable X M ⟶ diagonalizable X N)
    {g h : N →+ M} (hgh : g ≠ h) : Disjoint (homLocus f g) (homLocus f h) := by
  rw [disjoint_iff]
  ext x
  simp only [TopologicalSpace.Opens.coe_inf, Set.mem_inter_iff, SetLike.mem_coe,
    TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false, not_and]
  intro hx hx'
  obtain ⟨V, hxV, hV⟩ := mem_homLocus.mp hx
  obtain ⟨W, hxW, hW⟩ := mem_homLocus.mp hx'
  exact hgh (eq_of_dpull (show x ∈ V ⊓ W from ⟨hxV, hxW⟩)
    (dpull_of_le inf_le_left hV) (dpull_of_le inf_le_right hW))

theorem homLocus_cover [AddGroup.FG M] [AddGroup.FG N]
    (f : diagonalizable X M ⟶ diagonalizable X N) (x : X) :
    ∃ g : N →+ M, x ∈ homLocus f g := by
  obtain ⟨V, hx, g, hV⟩ := exists_open_dpull f x
  exact ⟨g, mem_homLocus.mpr ⟨V, hx, hV⟩⟩

/-- Restriction to the whole locus is the indicated character homomorphism. -/
theorem dpull_homLocus (f : diagonalizable X M ⟶ diagonalizable X N) (g : N →+ M) :
    dpull (homLocus f g).ι f = diagonalizableMap (homLocus f g) g := by
  apply dhom_ext
  intro x
  obtain ⟨V, hx, hV⟩ := mem_homLocus.mp x.property
  let W := (homLocus f g).ι ⁻¹ᵁ V
  have hc : W.ι ≫ (homLocus f g).ι =
      (homLocus f g).ι.resLE V W le_rfl ≫ V.ι :=
    (Scheme.Hom.resLE_comp_ι _ _).symm
  refine ⟨W, hx, ?_⟩
  rw [dpull_dpull_of_comm hc, hV, dpull_diagonalizableMap, dpull_diagonalizableMap]

/-- A surjective map of underlying bases detects equality of homomorphisms
between finitely generated diagonalizable groups. -/
theorem dpull_injective_of_surjective [AddGroup.FG M] [AddGroup.FG N]
    (b : Y ⟶ X) (hb : Function.Surjective b) :
    Function.Injective (dpull b :
      (diagonalizable X M ⟶ diagonalizable X N) →
        (diagonalizable Y M ⟶ diagonalizable Y N)) := by
  intro f g hfg
  apply dhom_ext
  intro x
  obtain ⟨V, hxV, p, hfV⟩ := exists_open_dpull f x
  obtain ⟨W, hxW, q, hgW⟩ := exists_open_dpull g x
  let U := V ⊓ W
  have hfU : dpull U.ι f = diagonalizableMap U p := dpull_of_le inf_le_left hfV
  have hgU : dpull U.ι g = diagonalizableMap U q := dpull_of_le inf_le_right hgW
  let U' := b ⁻¹ᵁ U
  have hc : U'.ι ≫ b = b.resLE U U' le_rfl ≫ U.ι :=
    (Scheme.Hom.resLE_comp_ι _ _).symm
  obtain ⟨y, hy⟩ := hb x
  have : Nonempty U' := ⟨⟨y, by change b y ∈ U; rw [hy]; exact ⟨hxV, hxW⟩⟩⟩
  have hpq := congrArg (dpull U'.ι) hfg
  rw [dpull_dpull_of_comm hc, dpull_dpull_of_comm hc, hfU, hgU,
    dpull_diagonalizableMap, dpull_diagonalizableMap] at hpq
  have hpq' : p = q := diagonalizableMap_injective hpq
  exact ⟨U, ⟨hxV, hxW⟩, hfU.trans (by rw [hpq']; exact hgU.symm)⟩

/-- Assemble character maps on any disjoint open decomposition of the base. -/
def assembleHom (U : (N →+ M) → X.Opens)
    [IsIso (Sigma.desc fun g : N →+ M => (U g).ι)] :
    diagonalizable X M ⟶ diagonalizable X N :=
  Descent.DisjointComponents.groupHom (fun g : N →+ M => (U g).ι) (fun g =>
    (diagonalizableBaseChangeIso (U g).ι M).hom ≫ diagonalizableMap (U g) g ≫
      (diagonalizableBaseChangeIso (U g).ι N).inv)

/-- The assembled homomorphism has the prescribed character map on every component. -/
@[simp] theorem dpull_assembleHom (U : (N →+ M) → X.Opens)
    [IsIso (Sigma.desc fun g : N →+ M => (U g).ι)] (g : N →+ M) :
    dpull (U g).ι (assembleHom U) = diagonalizableMap (U g) g := by
  rw [dpull_eq, assembleHom,
    Descent.DisjointComponents.map_groupHom (fun g : N →+ M => (U g).ι) _ g]
  simp

/-- The image of a character-map locus under a homeomorphism of base spaces. -/
def imageHomLocus (b : Y ⟶ X) (hb : IsHomeomorph b)
    (f : diagonalizable Y M ⟶ diagonalizable Y N) (g : N →+ M) : X.Opens :=
  ⟨b '' (homLocus f g), hb.isOpenMap _ (homLocus f g).isOpen⟩

theorem imageHomLocus_disjoint (b : Y ⟶ X) (hb : IsHomeomorph b)
    (f : diagonalizable Y M ⟶ diagonalizable Y N)
    {g h : N →+ M} (hgh : g ≠ h) :
    Disjoint (imageHomLocus b hb f g) (imageHomLocus b hb f h) := by
  apply TopologicalSpace.Opens.coe_disjoint.mp
  exact Set.disjoint_image_of_injective hb.injective
    (TopologicalSpace.Opens.coe_disjoint.mpr (homLocus_disjoint f hgh))

instance imageHomLocus_isIso [AddGroup.FG M] [AddGroup.FG N]
    (b : Y ⟶ X) (hb : IsHomeomorph b)
    (f : diagonalizable Y M ⟶ diagonalizable Y N) :
    IsIso (Sigma.desc fun g : N →+ M => (imageHomLocus b hb f g).ι) := by
  have hcol := nonempty_isColimit_cofanMk_of
    (fun g : N →+ M => (imageHomLocus b hb f g).ι) ?_ ?_
  · exact (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc _).mp hcol
  · rw [eq_top_iff]
    intro x _
    obtain ⟨y, rfl⟩ := hb.surjective x
    obtain ⟨g, hg⟩ := homLocus_cover f y
    simp only [Scheme.Opens.opensRange_ι]
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨g, y, hg, rfl⟩
  · intro g h hgh
    simp only [Function.onFun, Scheme.Opens.opensRange_ι]
    exact imageHomLocus_disjoint b hb f hgh

/-- Homomorphisms between finitely generated diagonalizable groups lift uniquely
along any base morphism that is a homeomorphism on underlying spaces. -/
theorem dpull_bijective_of_isHomeomorph [AddGroup.FG M] [AddGroup.FG N]
    (b : Y ⟶ X) (hb : IsHomeomorph b) :
    Function.Bijective (dpull b :
      (diagonalizable X M ⟶ diagonalizable X N) →
        (diagonalizable Y M ⟶ diagonalizable Y N)) := by
  refine ⟨dpull_injective_of_surjective b hb.surjective, ?_⟩
  intro f
  refine ⟨assembleHom (imageHomLocus b hb f), ?_⟩
  apply dhom_ext
  intro y
  obtain ⟨g, hg⟩ := homLocus_cover f y
  let V := homLocus f g
  let U := imageHomLocus b hb f g
  have hle : V ≤ b ⁻¹ᵁ U := fun z hz => ⟨z, hz, rfl⟩
  have hc : V.ι ≫ b = b.resLE U V hle ≫ U.ι :=
    (Scheme.Hom.resLE_comp_ι _ _).symm
  refine ⟨V, hg, ?_⟩
  rw [dpull_dpull_of_comm hc, dpull_assembleHom, dpull_diagonalizableMap, dpull_homLocus]

end Langlands.GroupScheme.RelativeMultiplicativeType
