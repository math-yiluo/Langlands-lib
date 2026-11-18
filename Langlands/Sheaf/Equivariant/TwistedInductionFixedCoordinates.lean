import Langlands.Sheaf.Equivariant.TwistedInductionSmoothCoordinates
import Langlands.Sheaf.PointProductSupport

/-!
# Fixed coordinates of twisted induction under a lifted subgroup action
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant.TwistedOver.InductionCoordinates

open CategoryTheory CategoryTheory.Limits Opposite

universe v u uG w

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C} [P.RespectsIso]
variable {X : C} {G : Type uG} [Group G] (ρ : G →* Aut X)

/-- The ordinary arrow underlying a twisted arrow between translated objects, with a
prescribed target label equal to the label used by `transport`. -/
def transportTo {U V : TwistedOver P ρ} (f : U ⟶ V) (g g' : G)
    (hg : g' = g * (Hom.twist f)⁻¹) :
    (translate P ρ g).obj U.obj ⟶ (translate P ρ g').obj V.obj :=
  MorphismProperty.Over.homMk (Hom.left (U := U) (V := V) f) (by
    change Hom.left (U := U) (V := V) f ≫ (V.hom ≫ (ρ g').hom) = U.hom ≫ (ρ g).hom
    rw [hg, ← Category.assoc, Hom.w, Category.assoc, ← rho_mul_hom, inv_mul_cancel_right])

@[simp]
theorem transportTo_left {U V : TwistedOver P ρ} (f : U ⟶ V) (g g' : G)
    (hg : g' = g * (Hom.twist f)⁻¹) :
    (transportTo ρ f g g' hg).left = Hom.left f :=
  rfl

/-- With the label of `transport`, the two ordinary arrows agree. -/
theorem transportTo_eq_transport {U V : TwistedOver P ρ} (f : U ⟶ V) (g : G) :
    transportTo ρ f g (g * (Hom.twist f)⁻¹) rfl = transport ρ f g :=
  rfl

section Lift

variable {U : TwistedOver P ρ} {H : Subgroup G} (a : H →* (End U)ᵐᵒᵖ)

omit [P.RespectsIso] in
/-- The underlying arrows of a local action compose according to the group law. -/
theorem left_comp_left (h k : H) :
    Hom.left (a h).unop ≫ Hom.left (a k).unop = Hom.left (a (h * k)).unop := by
  rw [← comp_left, map_mul, MulOpposite.unop_mul, End.mul_def]

omit [P.RespectsIso] in
/-- The identity element acts through the identity arrow. -/
theorem left_one : Hom.left (a 1).unop = 𝟙 U.obj.left := by
  rw [map_one, MulOpposite.unop_one, End.one_def, id_left]

/-- The element of `K` carrying `g` to the chosen representative `c.out` of a left coset
`c = gK`. -/
def cosetShift {K : Subgroup G} (g : G) (c : G ⧸ K) (hc : (g : G ⧸ K) = c) : K :=
  ⟨g⁻¹ * c.out, QuotientGroup.eq.mp (hc.trans (QuotientGroup.out_eq' c).symm)⟩

theorem mul_cosetShift {K : Subgroup G} (g : G) (c : G ⧸ K) (hc : (g : G ⧸ K) = c) :
    g * (cosetShift g c hc : G) = c.out :=
  mul_inv_cancel_left g c.out

variable {a}

omit [P.RespectsIso] in
/-- For a lift, the label of a transported coordinate is right multiplication by the acting
element. -/
theorem out_eq_mul_twist_inv (ha : IsLift a) {K : Subgroup G} (hKH : K ≤ H)
    (g : G) (c : G ⧸ K) (hc : (g : G ⧸ K) = c) :
    c.out = g * (Hom.twist (a ⟨cosetShift g c hc, hKH (cosetShift g c hc).2⟩).unop)⁻¹ := by
  rw [ha, inv_inv]
  exact (mul_cosetShift g c hc).symm

/-- The ordinary arrow from the coordinate at `g` to the coordinate at the chosen
representative of its coset. -/
def cosetTransport (ha : IsLift a) {K : Subgroup G} (hKH : K ≤ H)
    (g : G) (c : G ⧸ K) (hc : (g : G ⧸ K) = c) :
    (translate P ρ g).obj U.obj ⟶ (translate P ρ c.out).obj U.obj :=
  transportTo ρ (a ⟨cosetShift g c hc, hKH (cosetShift g c hc).2⟩).unop g c.out
    (out_eq_mul_twist_inv ρ ha hKH g c hc)

@[simp]
theorem cosetTransport_left (ha : IsLift a) {K : Subgroup G} (hKH : K ≤ H)
    (g : G) (c : G ⧸ K) (hc : (g : G ⧸ K) = c) :
    (cosetTransport ρ ha hKH g c hc).left =
      Hom.left (a ⟨cosetShift g c hc, hKH (cosetShift g c hc).2⟩).unop :=
  rfl

omit [P.RespectsIso] in
/-- The action of an element of `K` followed by the arrow to the representative is the arrow
to the representative. -/
theorem left_comp_cosetTransport_left (ha : IsLift a) {K : Subgroup G} (hKH : K ≤ H)
    (h : H) (g : G) (c : G ⧸ K) (hc : (g : G ⧸ K) = c)
    (hc' : ((g * (Hom.twist (a h).unop)⁻¹ : G) : G ⧸ K) = c) :
    Hom.left (a h).unop ≫
        Hom.left (a ⟨cosetShift (g * (Hom.twist (a h).unop)⁻¹) c hc',
          hKH (cosetShift _ c hc').2⟩).unop =
      Hom.left (a ⟨cosetShift g c hc, hKH (cosetShift g c hc).2⟩).unop := by
  rw [left_comp_left]
  congr 3
  apply Subtype.ext
  simp only [Subgroup.coe_mul, cosetShift, ha h, inv_inv, mul_inv_rev, ← mul_assoc,
    mul_inv_cancel, one_mul]

/-- The arrow from a representative to itself is the identity. -/
theorem cosetTransport_out (ha : IsLift a) {K : Subgroup G} (hKH : K ≤ H) (c : G ⧸ K)
    (hc : ((c.out : G) : G ⧸ K) = c) :
    cosetTransport ρ ha hKH c.out c hc = 𝟙 _ := by
  apply MorphismProperty.Over.Hom.ext
  rw [cosetTransport_left]
  have e : (⟨cosetShift c.out c hc, hKH (cosetShift c.out c hc).2⟩ : H) = 1 :=
    Subtype.ext (inv_mul_cancel c.out)
  rw [e, left_one]
  rfl

end Lift

variable {R : Type w} [CommRing R]
variable [∀ F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R,
  (ι P ρ).op.HasPointwiseRightKanExtension F]

section Fixed

variable (F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R) {U : TwistedOver P ρ} {H : Subgroup G}
variable (a : H →* (End U)ᵐᵒᵖ)

/-- The sections of the actual induction fixed by all elements of the acting subgroup which
lie in `K`, for the action by restriction along the local action. -/
def fixedSubmodule (K : Subgroup G) : Submodule R (((ι P ρ).op.ran.obj F).obj (op U)) :=
  ⨅ (h : H) (_ : (h : G) ∈ K),
    LinearMap.eqLocus (((ι P ρ).op.ran.obj F).map (a h).unop.op).hom LinearMap.id

omit [P.RespectsIso] in
theorem mem_fixedSubmodule_iff (K : Subgroup G) (s : ((ι P ρ).op.ran.obj F).obj (op U)) :
    s ∈ fixedSubmodule ρ F a K ↔
      ∀ h : H, (h : G) ∈ K → ((ι P ρ).op.ran.obj F).map (a h).unop.op s = s := by
  simp only [fixedSubmodule, Submodule.mem_iInf, LinearMap.mem_eqLocus, LinearMap.id_apply]

omit [P.RespectsIso] in
/-- Fixed submodules decrease as the fixing subgroup grows. -/
theorem fixedSubmodule_antitone {K K' : Subgroup G} (hKK' : K ≤ K') :
    fixedSubmodule ρ F a K' ≤ fixedSubmodule ρ F a K := fun s hs =>
  (mem_fixedSubmodule_iff ρ F a K s).2 fun h hh =>
    (mem_fixedSubmodule_iff ρ F a K' s).1 hs h (hKK' hh)

variable {a}

/-- A coordinate of a fixed section is the transport of the coordinate whose label is
translated by an element of `K`. -/
theorem projection_eq_of_mem_fixedSubmodule {K : Subgroup G}
    {s : ((ι P ρ).op.ran.obj F).obj (op U)} (hs : s ∈ fixedSubmodule ρ F a K)
    (h : H) (hh : (h : G) ∈ K) (g g' : G) (hg : g' = g * (Hom.twist (a h).unop)⁻¹) :
    projection ρ F U g s =
      F.map (transportTo ρ (a h).unop g g' hg).op (projection ρ F U g' s) := by
  subst hg
  have e : projection ρ F U g (((ι P ρ).op.ran.obj F).map (a h).unop.op s) =
      F.map (transport ρ (a h).unop g).op
        (projection ρ F U (g * (Hom.twist (a h).unop)⁻¹) s) :=
    congrArg (fun k => k.hom s) (map_projection ρ F (a h).unop g)
  rw [(mem_fixedSubmodule_iff ρ F a K s).1 hs h hh] at e
  exact e

/-- The coordinates of a fixed section at the chosen coset representatives. -/
def fixedCoordinateMap (K : Subgroup G) :
    fixedSubmodule ρ F a K →ₗ[R] ∀ c : G ⧸ K, ↑(objects ρ F U c.out) :=
  LinearMap.pi fun c => (projection ρ F U c.out).hom.comp (fixedSubmodule ρ F a K).subtype

@[simp]
theorem fixedCoordinateMap_apply (K : Subgroup G) (s : fixedSubmodule ρ F a K) (c : G ⧸ K) :
    fixedCoordinateMap ρ F K s c = projection ρ F U c.out s.val :=
  rfl

/-- A fixed section has its coordinate at `g` determined by the coordinate at the chosen
representative of `gK`. -/
theorem projection_eq_cosetTransport (ha : IsLift a) {K : Subgroup G} (hKH : K ≤ H)
    {s : ((ι P ρ).op.ran.obj F).obj (op U)} (hs : s ∈ fixedSubmodule ρ F a K)
    (g : G) (c : G ⧸ K) (hc : (g : G ⧸ K) = c) :
    projection ρ F U g s =
      F.map (cosetTransport ρ ha hKH g c hc).op (projection ρ F U c.out s) :=
  projection_eq_of_mem_fixedSubmodule ρ F hs _ (cosetShift g c hc).2 g c.out
    (out_eq_mul_twist_inv ρ ha hKH g c hc)

theorem fixedCoordinateMap_injective (ha : IsLift a) {K : Subgroup G} (hKH : K ≤ H) :
    Function.Injective (fixedCoordinateMap ρ F (a := a) K) := by
  intro s t hst
  apply Subtype.ext
  apply section_ext ρ F U
  intro g
  rw [projection_eq_cosetTransport ρ F ha hKH s.2 g _ rfl,
    projection_eq_cosetTransport ρ F ha hKH t.2 g _ rfl]
  exact congrArg _ (congrFun hst (g : G ⧸ K))

/-- The coordinate family spread from representative values along the cosets. -/
def spreadCoordinates (ha : IsLift a) {K : Subgroup G} (hKH : K ≤ H)
    (u : ∀ c : G ⧸ K, ↑(objects ρ F U c.out)) (g : G) : ↑(objects ρ F U g) :=
  F.map (cosetTransport ρ ha hKH g _ rfl).op (u (g : G ⧸ K))

omit [∀ F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R,
  (ι P ρ).op.HasPointwiseRightKanExtension F] in
theorem spreadCoordinates_eq (ha : IsLift a) {K : Subgroup G} (hKH : K ≤ H)
    (u : ∀ c : G ⧸ K, ↑(objects ρ F U c.out)) (g : G) (c : G ⧸ K)
    (hc : (g : G ⧸ K) = c) :
    spreadCoordinates ρ F ha hKH u g = F.map (cosetTransport ρ ha hKH g c hc).op (u c) := by
  subst hc
  rfl

/-- The section with prescribed representative coordinates, spread along the cosets. -/
def spreadSection (ha : IsLift a) {K : Subgroup G} (hKH : K ≤ H)
    (u : ∀ c : G ⧸ K, ↑(objects ρ F U c.out)) : ((ι P ρ).op.ran.obj F).obj (op U) :=
  (moduleCoordinates ρ F U).symm (spreadCoordinates ρ F ha hKH u)

theorem projection_spreadSection (ha : IsLift a) {K : Subgroup G} (hKH : K ≤ H)
    (u : ∀ c : G ⧸ K, ↑(objects ρ F U c.out)) (g : G) :
    projection ρ F U g (spreadSection ρ F ha hKH u) = spreadCoordinates ρ F ha hKH u g := by
  rw [← moduleCoordinates_apply, spreadSection, LinearEquiv.apply_symm_apply]

theorem spreadSection_mem (ha : IsLift a) {K : Subgroup G} (hKH : K ≤ H)
    (u : ∀ c : G ⧸ K, ↑(objects ρ F U c.out)) :
    spreadSection ρ F ha hKH u ∈ fixedSubmodule ρ F a K := by
  rw [mem_fixedSubmodule_iff]
  intro h hh
  apply section_ext ρ F U
  intro g
  have e : projection ρ F U g
        (((ι P ρ).op.ran.obj F).map (a h).unop.op (spreadSection ρ F ha hKH u)) =
      F.map (transport ρ (a h).unop g).op
        (projection ρ F U (g * (Hom.twist (a h).unop)⁻¹) (spreadSection ρ F ha hKH u)) :=
    congrArg (fun k => k.hom (spreadSection ρ F ha hKH u)) (map_projection ρ F (a h).unop g)
  rw [e, projection_spreadSection, projection_spreadSection]
  have hc' : ((g * (Hom.twist (a h).unop)⁻¹ : G) : G ⧸ K) = (g : G ⧸ K) := by
    rw [ha h, inv_inv]
    exact QuotientGroup.mk_mul_of_mem g hh
  rw [spreadCoordinates_eq ρ F ha hKH u _ (g : G ⧸ K) hc', spreadCoordinates_eq ρ F ha hKH u g _ rfl]
  have key : transport ρ (a h).unop g ≫ cosetTransport ρ ha hKH _ (g : G ⧸ K) hc' =
      cosetTransport ρ ha hKH g (g : G ⧸ K) rfl :=
    MorphismProperty.Over.Hom.ext (left_comp_cosetTransport_left ρ ha hKH h g _ rfl hc')
  rw [← key, op_comp, F.map_comp]
  rfl

theorem fixedCoordinateMap_surjective (ha : IsLift a) {K : Subgroup G} (hKH : K ≤ H) :
    Function.Surjective (fixedCoordinateMap ρ F (a := a) K) := by
  intro u
  refine ⟨⟨spreadSection ρ F ha hKH u, spreadSection_mem ρ F ha hKH u⟩, ?_⟩
  funext c
  rw [fixedCoordinateMap_apply, projection_spreadSection,
    spreadCoordinates_eq ρ F ha hKH u c.out c (QuotientGroup.out_eq' c),
    cosetTransport_out, op_id, F.map_id]
  rfl

/-- **Fixed coordinates.** For a lift `a` of `H` and a subgroup `K ≤ H`, the `K`-fixed
sections of the actual induction are free coordinate families indexed by the left cosets of
`K`, evaluated at their chosen representatives. -/
def fixedCoordinates (ha : IsLift a) {K : Subgroup G} (hKH : K ≤ H) :
    fixedSubmodule ρ F a K ≃ₗ[R] ∀ c : G ⧸ K, ↑(objects ρ F U c.out) :=
  LinearEquiv.ofBijective (fixedCoordinateMap ρ F K)
    ⟨fixedCoordinateMap_injective ρ F ha hKH, fixedCoordinateMap_surjective ρ F ha hKH⟩

@[simp]
theorem fixedCoordinates_apply (ha : IsLift a) {K : Subgroup G} (hKH : K ≤ H)
    (s : fixedSubmodule ρ F a K) (c : G ⧸ K) :
    fixedCoordinates ρ F ha hKH s c = projection ρ F U c.out s.val :=
  rfl

end Fixed

section Smooth

variable [TopologicalSpace G] (L : LocalActionSystem (TwistedOver P ρ) G)
variable (J : GrothendieckTopology (TwistedOver P ρ)) [L.HasAdmissibleRefinements J]
variable (F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R)

omit [P.RespectsIso] in
/-- A section is discrete for a local action exactly when it is fixed by some open subgroup
contained in the acting subgroup. -/
theorem isDiscreteSection_iff_exists_mem_fixedSubmodule {U : TwistedOver P ρ}
    {H : OpenSubgroup G} (a : (H : Subgroup G) →* (End U)ᵐᵒᵖ)
    (s : ((ι P ρ).op.ran.obj F).obj (op U)) :
    IsDiscreteSection ((ι P ρ).op.ran.obj F) a s ↔
      ∃ K : OpenSubgroup G, K ≤ H ∧ s ∈ fixedSubmodule ρ F a (K : Subgroup G) := by
  constructor
  · rintro ⟨K, hKH, hK⟩
    exact ⟨K, hKH, (mem_fixedSubmodule_iff ρ F a _ s).2 hK⟩
  · rintro ⟨K, hKH, hs⟩
    exact ⟨K, hKH, (mem_fixedSubmodule_iff ρ F a _ s).1 hs⟩

omit [P.RespectsIso] in
/-- Over an object with an admissible local action, a section fixed by an open subgroup of
the acting subgroup is locally discrete. -/
theorem fixedSubmodule_le_smoothSubmodule {U : TwistedOver P ρ} {H : OpenSubgroup G}
    {a : (H : Subgroup G) →* (End U)ᵐᵒᵖ} (ha : L.IsAdmissible U H a)
    (K : OpenSubgroup G) (hKH : K ≤ H) :
    fixedSubmodule ρ F a (K : Subgroup G) ≤
      LocalActionSystem.smoothSubmodule L J ((ι P ρ).op.ran.obj F) U := by
  intro s hs
  rw [LocalActionSystem.mem_smoothSubmodule_iff]
  refine J.superset_covering ?_ (J.top_mem U)
  intro W g _
  refine ⟨U, g, 𝟙 U, H, a, ha, ?_, Category.comp_id g⟩
  have e : ((ι P ρ).op.ran.obj F).map (𝟙 U).op s = s := by simp
  rw [e]
  exact (isDiscreteSection_iff_exists_mem_fixedSubmodule ρ F a s).2 ⟨K, hKH, hs⟩

end Smooth

section PointProduct

variable {J : GrothendieckTopology (P.Over ⊤ X)} {I : Type w} (points : I → J.Point.{w})
variable (M : I → ModuleCat.{w} R) {U : TwistedOver P ρ} {H : Subgroup G}
variable {a : H →* (End U)ᵐᵒᵖ}

/-- **Fixed coordinates of an induced point product.** For a lift `a` of `H` and `K ≤ H`,
the `K`-fixed sections of the actual induction of the point product of the `M i` are
arbitrary coefficient families on the point fibers of the translates of `U` by the chosen
representatives of the left cosets of `K`. -/
def pointProductFixedCoordinates (ha : IsLift a) {K : Subgroup G} (hKH : K ≤ H) :
    fixedSubmodule ρ (PointProduct.productSheaf points (ModuleCat.{w} R) M).obj a K ≃ₗ[R]
      ∀ (c : G ⧸ K) (i : I), (points i).fiber.obj ((translate P ρ c.out).obj U.obj) → M i :=
  (fixedCoordinates ρ _ ha hKH).trans
    (LinearEquiv.piCongrRight fun c =>
      PointProduct.sectionCoordinates points M ((translate P ρ c.out).obj U.obj))

@[simp]
theorem pointProductFixedCoordinates_apply (ha : IsLift a) {K : Subgroup G} (hKH : K ≤ H)
    (s : fixedSubmodule ρ (PointProduct.productSheaf points (ModuleCat.{w} R) M).obj a K)
    (c : G ⧸ K) (i : I) (x : (points i).fiber.obj ((translate P ρ c.out).obj U.obj)) :
    pointProductFixedCoordinates ρ points M ha hKH s c i x =
      PointProduct.sectionCoordinate points M ((translate P ρ c.out).obj U.obj) i x
        (projection ρ (PointProduct.productSheaf points (ModuleCat.{w} R) M).obj U c.out
          s.val) :=
  PointProduct.sectionCoordinates_apply points M _ _ i x

end PointProduct

end Langlands.Sheaf.Equivariant.TwistedOver.InductionCoordinates
