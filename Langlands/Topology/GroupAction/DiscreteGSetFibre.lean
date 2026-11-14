import Langlands.Topology.GroupAction.DiscreteGSetSite
import Langlands.Representation.Category.Basic
import Langlands.Representation.Smooth.SmoothPart.Definitions
import Mathlib.CategoryTheory.Elements
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.Topology.Algebra.OpenSubgroup

/-! # The fibre of a presheaf on `P(G)` as a smooth representation -/

noncomputable section

universe z w uR

open CategoryTheory Limits Opposite

namespace Langlands.DiscreteGSet

variable (G : Type z) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-! ## Orbits and pointed orbits -/

/-- The discrete `G`-set `G ⧸ N` of an open subgroup `N`. -/
abbrev orbit (N : OpenSubgroup G) : DiscreteGSet G :=
  quotient G N.toSubgroup N.isOpen

/-- The orbit category: open subgroups `N`, with the `G`-maps `G ⧸ N → G ⧸ N'` as
morphisms. -/
abbrev OrbitCategory := InducedCategory (DiscreteGSet G) (orbit G)

/-- The inclusion of the orbit category in `P(G)`. -/
abbrev orbitFunctor : OrbitCategory G ⥤ DiscreteGSet G :=
  inducedFunctor (orbit G)

/-- `N ↦ G ⧸ N` as a functor to sets. -/
abbrev orbitPoints : OrbitCategory G ⥤ Type z :=
  orbitFunctor G ⋙ forget G

/-- Pointed orbits: pairs `(N, a)` of an open subgroup `N` and a point `a ∈ G ⧸ N`; a
morphism `(N, a) ⟶ (N', a')` is a `G`-map `G ⧸ N → G ⧸ N'` sending `a` to `a'`. -/
abbrev PointedOrbit := (orbitPoints G).Elements

variable {G}

/-- The pointed orbit `(N, a)`. -/
abbrev PointedOrbit.mk (N : OpenSubgroup G) (a : G ⧸ N.toSubgroup) : PointedOrbit G :=
  Functor.elementsMk (orbitPoints G) N a

/-- The point `a ∈ G ⧸ N` of a pointed orbit `(N, a)`. -/
abbrev PointedOrbit.pt (x : PointedOrbit G) : G ⧸ (OpenSubgroup.toSubgroup x.obj) :=
  x.val

/-- The stabilizer of the point of a pointed orbit, an open subgroup of `G`. -/
def PointedOrbit.stabilizer (x : PointedOrbit G) : OpenSubgroup G where
  toSubgroup := MulAction.stabilizer G x.pt
  isOpen' := isOpen_stabilizer_quotient x.obj.isOpen x.pt

/-- The map `G ⧸ N → G ⧸ N'` of a morphism of the orbit category. -/
abbrev orbitMap {N N' : OrbitCategory G} (f : N ⟶ N') :
    G ⧸ (OpenSubgroup.toSubgroup N) → G ⧸ (OpenSubgroup.toSubgroup N') :=
  fun a => (orbitPoints G).map f a

/-- The maps of the orbit category commute with the action of `G`. -/
theorem orbitMap_smul {N N' : OrbitCategory G} (f : N ⟶ N') (g : G)
    (a : G ⧸ (OpenSubgroup.toSubgroup N)) :
    orbitMap f (g • a) = g • orbitMap f a :=
  (Action.gMap f.hom.hom).map_smul' g a

/-- A morphism of the orbit category is determined by its map of sets. -/
theorem orbitCategory_hom_ext {N N' : OrbitCategory G} {f f' : N ⟶ N'}
    (h : ∀ a, orbitMap f a = orbitMap f' a) : f = f' :=
  (orbitPoints G).map_injective (ConcreteCategory.hom_ext _ _ h)

/-- There is at most one morphism between two pointed orbits: `G ⧸ N` is the orbit of its
point. -/
theorem PointedOrbit.hom_ext {x y : PointedOrbit G} (f f' : x ⟶ y) : f = f' := by
  refine Functor.Elements.hom_ext (orbitCategory_hom_ext fun a => ?_)
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G x.pt a
  rw [orbitMap_smul, orbitMap_smul]
  exact congrArg (g • ·) (f.map_val.trans f'.map_val.symm)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The `G`-map `G ⧸ N → S`, `gN ↦ g • s`, for `N` contained in the stabilizer of `s`. -/
def quotientGMap {S : Type*} [MulAction G S] {N : Subgroup G} (s : S)
    (h : N ≤ MulAction.stabilizer G s) : G ⧸ N →[G] S where
  toFun x := Quotient.liftOn' x (fun g => g • s) fun g₁ g₂ hg => by
    have hs : (g₁⁻¹ * g₂) • s = s := h (QuotientGroup.leftRel_apply.mp hg)
    rw [mul_smul, inv_smul_eq_iff] at hs
    exact hs.symm
  map_smul' g x := by
    induction x using QuotientGroup.induction_on with
    | H k => exact mul_smul g k s

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp]
theorem quotientGMap_mk {S : Type*} [MulAction G S] {N : Subgroup G} (s : S)
    (h : N ≤ MulAction.stabilizer G s) (g : G) :
    quotientGMap s h (g : G ⧸ N) = g • s :=
  rfl

/-- The morphism `G ⧸ N → G ⧸ N'`, `gN ↦ g • a`, of the orbit category, for `N` contained in
the stabilizer of `a`. -/
def orbitHom {N N' : OrbitCategory G} (a : G ⧸ (OpenSubgroup.toSubgroup N'))
    (h : OpenSubgroup.toSubgroup N ≤ MulAction.stabilizer G a) : N ⟶ N' :=
  InducedCategory.homMk (ObjectProperty.homMk
    { hom := TypeCat.ofHom (quotientGMap a h)
      comm := fun g => ConcreteCategory.hom_ext _ _ fun x => (quotientGMap a h).map_smul g x })

@[simp]
theorem orbitMap_orbitHom {N N' : OrbitCategory G} (a : G ⧸ (OpenSubgroup.toSubgroup N'))
    (h : OpenSubgroup.toSubgroup N ≤ MulAction.stabilizer G a) (x : G ⧸ OpenSubgroup.toSubgroup N) :
    orbitMap (orbitHom a h) x = quotientGMap a h x :=
  rfl

/-- Translation of pointed orbits by `g ∈ G`: `(N, a) ↦ (N, g • a)`. -/
@[simps]
def translate (g : G) : PointedOrbit G ⥤ PointedOrbit G where
  obj x := PointedOrbit.mk x.obj (g • x.pt)
  map {x y} f := Functor.Elements.homMk f.hom (by
    change orbitMap f.hom (g • x.pt) = g • y.pt
    rw [orbitMap_smul]
    exact congrArg (g • ·) f.map_val)
  map_id _ := rfl
  map_comp _ _ := rfl

/-! ## Base points of the orbits `G ⧸ N` -/

variable (G) in
/-- `N ↦ (N, [1])`, from the open subgroups ordered by inclusion to the pointed orbits; for
`N ≤ N'` the morphism is the projection `G ⧸ N → G ⧸ N'`. -/
def basePoint : OpenSubgroup G ⥤ PointedOrbit G where
  obj N := PointedOrbit.mk N ((1 : G) : G ⧸ N.toSubgroup)
  map {N N'} f := Functor.Elements.homMk
    (orbitHom (N := N) (N' := N') ((1 : G) : G ⧸ N'.toSubgroup) (by
      rw [MulAction.stabilizer_quotient]
      exact OpenSubgroup.toSubgroup_le.mpr (leOfHom f)))
    ((orbitMap_orbitHom _ _ _).trans (one_smul G _))
  map_id _ := PointedOrbit.hom_ext _ _
  map_comp _ _ := PointedOrbit.hom_ext _ _

/-- The morphism `(G_a, [1]) ⟶ (N, a)`, `g G_a ↦ g • a`, out of the base point of the
stabilizer `G_a` of `a`. -/
def basePointHom (x : PointedOrbit G) : (basePoint G).obj x.stabilizer ⟶ x :=
  Functor.Elements.homMk
    (orbitHom (N := ((basePoint G).obj x.stabilizer).obj) (N' := x.obj) x.pt (le_of_eq rfl))
    ((orbitMap_orbitHom _ _ _).trans (one_smul G _))

/-- The base points are final among the pointed orbits (in the opposite categories): every
pointed orbit receives a morphism from a base point, and morphisms of pointed orbits are
unique. -/
instance final_basePoint_op : (basePoint G).op.Final :=
  Functor.final_of_exists_of_isFiltered _
    (fun d => ⟨op d.unop.stabilizer, ⟨(basePointHom d.unop).op⟩⟩)
    (fun {_ c} s s' => ⟨c, 𝟙 c, by rw [Quiver.Hom.unop_inj (PointedOrbit.hom_ext s.unop s'.unop)]⟩)

/-! ## The fibre and its `G`-action -/

section Fibre

variable {C : Type*} [Category C] (P : (DiscreteGSet G)ᵒᵖ ⥤ C)

/-- The diagram `(N, a) ↦ P(G ⧸ N)` over the opposite of the pointed orbits. -/
abbrev fibreDiagram : (PointedOrbit G)ᵒᵖ ⥤ C :=
  (Functor.Elements.π (orbitPoints G) ⋙ orbitFunctor G).op ⋙ P

variable [HasColimitsOfShape (PointedOrbit G)ᵒᵖ C]

/-- The fibre of a presheaf `P` on `P(G)`: the colimit of `P(G ⧸ N)` over the pointed
orbits `(N, a)`. -/
abbrev fibre : C :=
  colimit (fibreDiagram P)

/-- **Berkovich's description of the fibre** (1996, §1.2): the colimit of the `P(G ⧸ N)`
over the open subgroups `N`, ordered by reverse inclusion with the restrictions along the
projections `G ⧸ N → G ⧸ N'`, is the fibre. -/
def colimitOpenSubgroupIsoFibre : colimit ((basePoint G).op ⋙ fibreDiagram P) ≅ fibre P :=
  Functor.Final.colimitIso (basePoint G).op (fibreDiagram P)

@[reassoc (attr := simp)]
theorem ι_colimitOpenSubgroupIsoFibre_hom (N : OpenSubgroup G) :
    colimit.ι ((basePoint G).op ⋙ fibreDiagram P) (op N) ≫ (colimitOpenSubgroupIsoFibre P).hom =
      colimit.ι (fibreDiagram P) (op ((basePoint G).obj N)) :=
  Functor.Final.ι_colimitIso_hom _ _ _

/-- The colimit injection at `(N, a)` depends only on `N` and the point `a`. -/
theorem ι_congr {N : OpenSubgroup G} {a b : G ⧸ N.toSubgroup} (h : a = b) :
    colimit.ι (fibreDiagram P) (op (PointedOrbit.mk N a)) =
      colimit.ι (fibreDiagram P) (op (PointedOrbit.mk N b)) := by
  subst h
  rfl

/-- The action of `g ∈ G` on the fibre: the injection at `(N, a)` is sent to the injection
at `(N, g • a)`. -/
def fibreAct (g : G) : fibre P ⟶ fibre P :=
  colimit.desc (fibreDiagram P)
    { pt := fibre P
      ι :=
        { app := fun x => colimit.ι (fibreDiagram P) (op ((translate g).obj x.unop))
          naturality := fun x y f => by
            exact (colimit.w (fibreDiagram P) ((translate g).map f.unop).op).trans
              (Category.comp_id _).symm } }

@[reassoc (attr := simp)]
theorem ι_fibreAct (x : PointedOrbit G) (g : G) :
    colimit.ι (fibreDiagram P) (op x) ≫ fibreAct P g =
      colimit.ι (fibreDiagram P) (op ((translate g).obj x)) :=
  colimit.ι_desc _ _

theorem fibreAct_one : fibreAct P 1 = 𝟙 (fibre P) := by
  refine colimit.hom_ext fun j => ?_
  obtain ⟨x⟩ := j
  rw [ι_fibreAct, Category.comp_id]
  exact ι_congr P (one_smul G x.pt)

theorem fibreAct_mul (g h : G) : fibreAct P (g * h) = fibreAct P h ≫ fibreAct P g := by
  refine colimit.hom_ext fun j => ?_
  obtain ⟨x⟩ := j
  rw [ι_fibreAct, ι_fibreAct_assoc]
  exact (ι_congr P (mul_smul g h x.pt)).trans (ι_fibreAct P ((translate h).obj x) g).symm

variable {P}

/-- The map of fibres induced by a morphism of presheaves on `P(G)`. -/
abbrev fibreMap {Q : (DiscreteGSet G)ᵒᵖ ⥤ C} (α : P ⟶ Q) : fibre P ⟶ fibre Q :=
  colimMap (Functor.whiskerLeft (Functor.Elements.π (orbitPoints G) ⋙ orbitFunctor G).op α)

theorem fibreMap_id : fibreMap (𝟙 P) = 𝟙 (fibre P) :=
  colimit.hom_ext fun j => by simp

theorem fibreMap_comp {Q S : (DiscreteGSet G)ᵒᵖ ⥤ C} (α : P ⟶ Q) (β : Q ⟶ S) :
    fibreMap (α ≫ β) = fibreMap α ≫ fibreMap β :=
  colimit.hom_ext fun j => by simp

/-- The maps of fibres commute with the action of `G`. -/
@[reassoc]
theorem fibreAct_fibreMap {Q : (DiscreteGSet G)ᵒᵖ ⥤ C} (α : P ⟶ Q) (g : G) :
    fibreAct P g ≫ fibreMap α = fibreMap α ≫ fibreAct Q g := by
  refine colimit.hom_ext fun j => ?_
  obtain ⟨x⟩ := j
  rw [ι_fibreAct_assoc, ι_colimMap_assoc, ι_fibreAct]
  exact ι_colimMap _ _

end Fibre

/-! ## The fibre of a presheaf of modules is a smooth representation -/

section Module

variable {R : Type uR} [CommRing R] (P : (DiscreteGSet G)ᵒᵖ ⥤ ModuleCat.{w} R)
  [HasColimitsOfShape (PointedOrbit G)ᵒᵖ (ModuleCat.{w} R)]

/-- The action of `G` on the fibre of a presheaf of `R`-modules on `P(G)`. -/
def fibreRepresentation : Representation R G (fibre P : ModuleCat.{w} R) where
  toFun g := (fibreAct P g).hom
  map_one' := by
    rw [fibreAct_one]
    rfl
  map_mul' g h := by
    rw [fibreAct_mul]
    rfl

theorem fibreRepresentation_apply (g : G) (v : (fibre P : ModuleCat.{w} R)) :
    fibreRepresentation P g v = (fibreAct P g).hom v :=
  rfl

theorem fibreRepresentation_ι_apply (x : PointedOrbit G) (g : G)
    (y : (fibreDiagram P).obj (op x)) :
    fibreRepresentation P g ((colimit.ι (fibreDiagram P) (op x)).hom y) =
      (colimit.ι (fibreDiagram P) (op ((translate g).obj x))).hom y := by
  rw [fibreRepresentation_apply, ← ModuleCat.comp_apply, ι_fibreAct]
  rfl

/-- The image of `P(G ⧸ N)` in the fibre is fixed by the stabilizer of the point. -/
theorem ι_apply_mem_fixedVectors (x : PointedOrbit G) (y : (fibreDiagram P).obj (op x)) :
    (colimit.ι (fibreDiagram P) (op x)).hom y ∈
      fixedVectors (fibreRepresentation P) x.stabilizer.toSubgroup := by
  rintro ⟨k, hk⟩
  change fibreRepresentation P k _ = _
  rw [fibreRepresentation_ι_apply]
  exact congrArg (fun f => (ModuleCat.Hom.hom f) y)
    (ι_congr P (N := x.obj) (MulAction.mem_stabilizer_iff.mp hk))

/-- **Smoothness of the fibre.** Every vector of the fibre has an open stabilizer: the
smooth vectors form a submodule containing the image of every `P(G ⧸ N)`, and these images
generate the colimit. -/
theorem isSmooth_fibreRepresentation : IsSmooth (fibreRepresentation P) := by
  let S := smoothVectors (fibreRepresentation P)
  have hle : ∀ (x : PointedOrbit G) (y : (fibreDiagram P).obj (op x)),
      (colimit.ι (fibreDiagram P) (op x)).hom y ∈ S := fun x y =>
    ⟨x.stabilizer, ι_apply_mem_fixedVectors P x y⟩
  have h0 : (ModuleCat.ofHom S.mkQ :
      fibre P ⟶ ModuleCat.of R ((fibre P : ModuleCat.{w} R) ⧸ S)) = 0 := by
    refine colimit.hom_ext fun j => ?_
    obtain ⟨x⟩ := j
    ext y
    simpa [Submodule.Quotient.mk_eq_zero] using hle x y
  intro v
  have hv := congrArg (fun f => ModuleCat.Hom.hom f v) h0
  have hv' : v ∈ S := by simpa [Submodule.Quotient.mk_eq_zero] using hv
  exact hv'

/-- The fibre of a presheaf of `R`-modules on `P(G)`, as a smooth representation of `G`. -/
abbrev fibreRep : SmoothRep.{uR, z, w} R G :=
  SmoothRep.of (fibreRepresentation P) (isSmooth_fibreRepresentation P)

variable {P}

/-- The intertwiner of fibres induced by a morphism of presheaves of modules. -/
def fibreIntertwiningMap {Q : (DiscreteGSet G)ᵒᵖ ⥤ ModuleCat.{w} R} (α : P ⟶ Q) :
    (fibreRepresentation P).IntertwiningMap (fibreRepresentation Q) where
  toLinearMap := (fibreMap α).hom
  isIntertwining' g := congrArg ModuleCat.Hom.hom (fibreAct_fibreMap α g)

variable (G R)

/-- **The fibre functor** of presheaves of `R`-modules on `P(G)` to smooth representations:
`P ↦ colim_{(N, a)} P(G ⧸ N)` with `G` acting by translation of the points. -/
def fibreFunctor :
    ((DiscreteGSet G)ᵒᵖ ⥤ ModuleCat.{w} R) ⥤ SmoothRep.{uR, z, w} R G where
  obj P := fibreRep P
  map α := SmoothRep.ofHom (fibreIntertwiningMap α)
  map_id P := by
    have h : fibreIntertwiningMap (𝟙 P) =
        Representation.IntertwiningMap.id (fibreRepresentation P) :=
      Representation.IntertwiningMap.ext (congrArg ModuleCat.Hom.hom (fibreMap_id (P := P)))
    rw [h]
    rfl
  map_comp α β := by
    have h : fibreIntertwiningMap (α ≫ β) =
        (fibreIntertwiningMap β).comp (fibreIntertwiningMap α) :=
      Representation.IntertwiningMap.ext (congrArg ModuleCat.Hom.hom (fibreMap_comp α β))
    rw [h]
    rfl

variable {G R}

@[simp]
theorem fibreFunctor_obj (P : (DiscreteGSet G)ᵒᵖ ⥤ ModuleCat.{w} R) :
    (fibreFunctor G R).obj P = fibreRep P :=
  rfl

theorem fibreFunctor_map_hom {P Q : (DiscreteGSet G)ᵒᵖ ⥤ ModuleCat.{w} R} (α : P ⟶ Q)
    (v : (fibre P : ModuleCat.{w} R)) :
    SmoothRep.hom ((fibreFunctor G R).map α) v = (fibreMap α).hom v :=
  rfl

end Module

section Existence

variable (G) (R : Type uR) [CommRing R]

/-- Colimits over the pointed orbits exist in `R`-modules of universe `max z w`. -/
theorem hasColimitsOfShape_pointedOrbit :
    HasColimitsOfShape (PointedOrbit G)ᵒᵖ (ModuleCat.{max z w} R) :=
  haveI : Small.{max z w} (PointedOrbit G)ᵒᵖ := small_lift.{z, w, z} _
  ModuleCat.hasColimitsOfShape (J := (PointedOrbit G)ᵒᵖ) (R := R)

end Existence

end Langlands.DiscreteGSet
