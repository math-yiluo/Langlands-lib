import Langlands.AlgebraicGeometry.Modules.RelativeFlatness
import Mathlib.Topology.Sheaves.Skyscraper
import Mathlib.Algebra.Category.Grp.Zero

/-! # Stalks of module sheaves and their skyscraper right adjoint -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace Langlands.AlgebraicGeometry.Modules

variable {X : Scheme.{u}}

/-- The canonical module stalk as a functor to modules over the source local ring. -/
def stalkFunctor (x : X) : X.Modules ⥤ ModuleCat.{u} (X.presheaf.stalk x) where
  obj M := ModuleCat.of _ (stalk M x)
  map φ := ModuleCat.ofHom (stalkMap φ x)
  map_id M := by
    ext m
    exact ConcreteCategory.congr_hom ((Scheme.Modules.toPresheaf X ⋙
      TopCat.Presheaf.stalkFunctor Ab.{u} x).map_id M) m
  map_comp φ ψ := by
    ext m
    exact ConcreteCategory.congr_hom ((Scheme.Modules.toPresheaf X ⋙
      TopCat.Presheaf.stalkFunctor Ab.{u} x).map_comp φ ψ) m

namespace StalkAdjunction

variable (x : X) (N : ModuleCat.{u} (X.presheaf.stalk x))

/-- Sections of a skyscraper module; the empty product is the zero group. -/
abbrev sections (U : X.Opens) := (hx : PLift (x ∈ U)) → N

instance sectionsModule (U : X.Opens) : Module Γ(X, U) (sections x N U) :=
  @Pi.module (PLift (x ∈ U)) (fun _ => N) Γ(X, U) inferInstance
    (fun _ => inferInstance) (fun hx => Module.compHom N (X.presheaf.germ U x hx.down).hom)

@[simp]
lemma sections_smul_apply (U : X.Opens) (r : Γ(X, U)) (n : sections x N U) (hx : PLift (x ∈ U)) :
    (r • n) hx = X.presheaf.germ U x hx.down r • n hx := rfl

/-- The actual presheaf of modules with skyscraper sections. -/
def presheaf : X.PresheafOfModules where
  obj U := by
    letI := sectionsModule x N U.unop
    exact ModuleCat.of Γ(X, U.unop) (sections x N U.unop)
  map {U V} i := by
    letI := sectionsModule x N U.unop
    letI := sectionsModule x N V.unop
    letI : Module Γ(X, U.unop) (sections x N V.unop) :=
      Module.compHom _ (X.presheaf.map i).hom
    refine ModuleCat.ofHom ?_
    refine { toFun := fun (n : sections x N U.unop) hx => n ⟨i.unop.le hx.down⟩
             map_add' := fun _ _ => rfl
             map_smul' := ?_ }
    intro r n
    funext hx
    change X.presheaf.germ U.unop x (i.unop.le hx.down) r • n _ =
      X.presheaf.germ V.unop x hx.down (X.presheaf.map i r) • n _
    erw [X.presheaf.germ_res_apply i.unop x hx.down r]

  map_id U := by ext; rfl
  map_comp f g := by ext; rfl

/-- Evaluation identifies nonempty skyscraper sections with their value. -/
def sectionsIso (U : X.Opens) (hx : x ∈ U) :
    AddCommGrpCat.of (sections x N U) ≅ AddCommGrpCat.of N :=
  { hom := AddCommGrpCat.ofHom
      { toFun := fun n => n ⟨hx⟩
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    inv := AddCommGrpCat.ofHom
      { toFun := fun n _ => n
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    hom_inv_id := by
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro n
      funext h
      rfl
    inv_hom_id := by ext n; rfl }

local instance (U : X.Opens) : Decidable (x ∈ U) := Classical.propDecidable _

/-- The underlying presheaf is the usual abelian skyscraper presheaf. -/
def presheafIso : (presheaf x N).presheaf ≅ skyscraperPresheaf x (AddCommGrpCat.of N) := by
  classical
  refine NatIso.ofComponents (fun U => ?_) ?_
  · by_cases hx : x ∈ U.unop
    · exact sectionsIso x N U.unop hx ≪≫ eqToIso (by simp [skyscraperPresheaf_obj, hx])
    · haveI : IsEmpty (PLift (x ∈ U.unop)) := ⟨fun h => hx h.down⟩
      exact (AddCommGrpCat.isZero_of_subsingleton
        (AddCommGrpCat.of (sections x N U.unop))).isTerminal.uniqueUpToIso
          (by simpa [skyscraperPresheaf_obj, hx] using
            (terminalIsTerminal : IsTerminal (terminal AddCommGrpCat.{u})))
  · intro U V i
    by_cases hxV : x ∈ V.unop
    · have hxU : x ∈ U.unop := i.unop.le hxV
      simp only [hxU, hxV, dite_eq_left]
      ext n
      simp [sectionsIso, skyscraperPresheaf_map, hxV]
      dsimp [presheaf]
      rfl
    · have ht : IsTerminal ((skyscraperPresheaf x (AddCommGrpCat.of N)).obj V) := by
        simpa [skyscraperPresheaf_obj, hxV] using
          (terminalIsTerminal : IsTerminal (terminal AddCommGrpCat.{u}))
      exact ht.hom_ext _ _

/-- A module over the local ring defines an actual skyscraper module sheaf. -/
def skyscraper : X.Modules where
  val := presheaf x N
  isSheaf := by
    apply (TopCat.Presheaf.isSheaf_iso_iff (presheafIso x N)).2
    exact skyscraperPresheaf_isSheaf x (AddCommGrpCat.of N)

variable {N}

/-- A local-ring linear map acts pointwise on skyscraper sections. -/
def skyscraperMap {N' : ModuleCat.{u} (X.presheaf.stalk x)} (φ : N ⟶ N') :
    skyscraper x N ⟶ skyscraper x N' where
  val :=
    { app := fun U => by
        letI := sectionsModule x N U.unop
        letI := sectionsModule x N' U.unop
        refine ModuleCat.ofHom (R := Γ(X, U.unop))
          { toFun := fun (n : sections x N U.unop) hx => φ (n hx)
            map_add' := by intros; funext hx; exact φ.hom.map_add _ _
            map_smul' := ?_ }
        intro r n
        funext hx
        exact φ.hom.map_smul (X.presheaf.germ U.unop x hx.down r) (n hx)
      naturality := by intros; ext n; rfl }

/-- The skyscraper construction is functorial in its local-ring module. -/
def skyscraperFunctor : ModuleCat.{u} (X.presheaf.stalk x) ⥤ X.Modules where
  obj := skyscraper x
  map := skyscraperMap x
  map_id _ := by ext U n; rfl
  map_comp _ _ := by ext U n; rfl

variable {M : X.Modules}

/-- A linear map from a stalk gives a map into the skyscraper by taking germs. -/
def toSkyscraper (L : (stalkFunctor x).obj M ⟶ N) : M ⟶ skyscraper x N where
  val :=
    { app := fun U => by
        letI := sectionsModule x N U.unop
        refine ModuleCat.ofHom (R := Γ(X, U.unop))
          { toFun := fun (m : Γ(M, U.unop)) hx => L (M.presheaf.germ U.unop x hx.down m)
            map_add' := by intros; funext hx; simp
            map_smul' := ?_ }
        intro r m
        funext hx
        change L (M.presheaf.germ U.unop x hx.down (r • m)) =
          X.presheaf.germ U.unop x hx.down r • L (M.presheaf.germ U.unop x hx.down m)
        erw [PresheafOfModules.germ_smul]
        exact L.hom.map_smul _ _
      naturality := by
        intro U V i
        ext m
        funext hx
        change L (M.presheaf.germ V.unop x hx.down (M.presheaf.map i m)) =
          L (M.presheaf.germ U.unop x (i.unop.le hx.down) m)
        erw [M.presheaf.germ_res_apply i.unop] }

/-- Evaluation of a skyscraper-valued map supplies a cocone on neighborhoods. -/
def evalCocone (φ : M ⟶ skyscraper x N) :
    Cocone ((OpenNhds.inclusion x).op ⋙ M.presheaf) where
  pt := AddCommGrpCat.of N
  ι :=
    { app := fun U => AddCommGrpCat.ofHom
        { toFun := fun m => (φ.app U.unop.1 m) ⟨U.unop.2⟩
          map_zero' := by rw [map_zero]; rfl
          map_add' := by intros; rw [map_add]; rfl }
      naturality := by
        intro U V i
        ext m
        have h := PresheafOfModules.naturality_apply φ.val
          ((OpenNhds.inclusion x).op.map i) m
        exact congrFun h ⟨V.unop.2⟩ }

/-- The additive map out of a stalk induced by evaluation on neighborhoods. -/
def fromStalkAdd (φ : M ⟶ skyscraper x N) : M.presheaf.stalk x ⟶ AddCommGrpCat.of N :=
  colimit.desc _ (evalCocone x φ)

@[simp]
lemma fromStalkAdd_germ (φ : M ⟶ skyscraper x N) (U : X.Opens) (hx : x ∈ U)
    (m : Γ(M, U)) : fromStalkAdd x φ (M.presheaf.germ U x hx m) = φ.app U m ⟨hx⟩ := by
  exact ConcreteCategory.congr_hom (colimit.ι_desc (evalCocone x φ) (op ⟨U, hx⟩)) m

/-- The map induced by evaluation is linear over the actual local ring. -/
def fromStalk (φ : M ⟶ skyscraper x N) : (stalkFunctor x).obj M ⟶ N :=
  ModuleCat.ofHom
    { toFun := fromStalkAdd x φ
      map_add' := map_add _
      map_smul' := by
        intro r m
        dsimp only [stalk, Scheme.Modules.presheaf] at *
        obtain ⟨U, hxU, r, rfl⟩ := X.presheaf.exists_germ_eq r
        obtain ⟨V, hVU, hxV, m, rfl⟩ := M.presheaf.exists_le_germ_eq m hxU
        rw [← X.presheaf.germ_res_apply (homOfLE hVU) x hxV r]
        erw [← PresheafOfModules.germ_smul M.val x V hxV]
        erw [fromStalkAdd_germ, fromStalkAdd_germ]
        have h := φ.val.app (op V) |>.hom.map_smul (X.presheaf.map (homOfLE hVU).op r) m
        exact congrFun h ⟨hxV⟩ }

@[simp]
lemma fromStalk_germ (φ : M ⟶ skyscraper x N) (U : X.Opens) (hx : x ∈ U)
    (m : Γ(M, U)) : fromStalk x φ (M.presheaf.germ U x hx m) = φ.app U m ⟨hx⟩ :=
  fromStalkAdd_germ x φ U hx m

/-- The stalk and skyscraper maps are inverse on hom sets. -/
def homEquiv (M : X.Modules) (N : ModuleCat.{u} (X.presheaf.stalk x)) :
    ((stalkFunctor x).obj M ⟶ N) ≃ (M ⟶ skyscraper x N) where
  toFun := toSkyscraper x
  invFun := fromStalk x
  left_inv L := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    obtain ⟨U, hx, m, rfl⟩ := M.presheaf.exists_germ_eq m
    rw [fromStalk_germ]
    rfl
  right_inv φ := by
    apply Scheme.Modules.hom_ext
    intro U
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro m
    funext hx
    exact fromStalk_germ x φ U hx.down m

/-- The canonical module-stalk functor is left adjoint to skyscraper modules. -/
def adjunction : stalkFunctor x ⊣ skyscraperFunctor x :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv x
      homEquiv_naturality_left_symm := by
        intro M' M N φ ψ
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro m
        obtain ⟨U, hx, m, rfl⟩ := M'.presheaf.exists_germ_eq m
        change fromStalk x (φ ≫ ψ) _ = fromStalk x ψ (stalkMap φ x _)
        rw [fromStalk_germ]
        change _ = fromStalk x ψ
          (((TopCat.Presheaf.stalkFunctor Ab.{u} x).map φ.mapPresheaf)
            (M'.presheaf.germ U x hx m))
        erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
        rw [fromStalk_germ]
        rfl
      homEquiv_naturality_right := by
        intro M N N' L φ
        ext U m
        rfl }

end StalkAdjunction

end Langlands.AlgebraicGeometry.Modules
