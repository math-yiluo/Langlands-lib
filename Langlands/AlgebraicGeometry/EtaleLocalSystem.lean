import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.GroupTheory.Finiteness
import Mathlib.Topology.ContinuousMap.LocallyConstant

/-! # Actual abelian étale local systems on the big relative site -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.EtaleLocalSystem

universe u v

variable {S T U : Scheme.{u}}

/-- The big étale topology on all schemes over `S`. -/
abbrev topology (S : Scheme.{u}) : GrothendieckTopology (Over S) :=
  Scheme.etaleTopology.over S

/-- Restriction to schemes over `T`, by composing their structure maps with `g`. -/
def restrict (g : T ⟶ S) (F : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{v}) :
    (Over T)ᵒᵖ ⥤ AddCommGrpCat.{v} :=
  (Over.map g).op ⋙ F

/-- Restriction transports natural isomorphisms. -/
def restrictIso (g : T ⟶ S) {F G : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{v}}
    (e : F ≅ G) : restrict g F ≅ restrict g G :=
  Functor.isoWhiskerLeft (Over.map g).op e

/-- Restriction along the identity is canonically the original presheaf. -/
def restrictIdIso (F : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{v}) : restrict (𝟙 S) F ≅ F :=
  Functor.isoWhiskerRight (NatIso.op (Over.mapId S)).symm F ≪≫ Functor.leftUnitor F

/-- Restriction along a composite agrees with successive restriction. -/
def restrictCompIso (g : T ⟶ S) (h : U ⟶ T)
    (F : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{v}) :
    restrict (h ≫ g) F ≅ restrict h (restrict g F) :=
  Functor.isoWhiskerRight (NatIso.op (Over.mapComp h g)).symm F ≪≫
    Functor.associator (Over.map h).op (Over.map g).op F

/-- Equal base morphisms give canonically isomorphic restrictions. -/
def restrictCongrIso {g h : T ⟶ S} (w : g = h)
    (F : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{v}) : restrict g F ≅ restrict h F :=
  Functor.isoWhiskerRight (NatIso.op (Over.mapCongr g h w)).symm F

/-- The actual constant abelian presheaf: continuous maps to discrete `M`. -/
def constant (S : Scheme.{u}) (M : AddCommGrpCat.{v}) :
    (Over S)ᵒᵖ ⥤ AddCommGrpCat.{max u v} := by
  letI : TopologicalSpace M := ⊥
  letI : DiscreteTopology M := discreteTopology_bot M
  exact (Over.forget S).op ⋙ continuousMapPresheafAb M

/-- Sections of `constant S M` are exactly locally constant `M`-valued functions. -/
def constantSections (S : Scheme.{u}) (M : AddCommGrpCat.{v}) (V : Over S) :
    (constant S M).obj (op V) ≃+ LocallyConstant V.left M := by
  letI : TopologicalSpace M := ⊥
  letI : DiscreteTopology M := discreteTopology_bot M
  change C(V.left, M) ≃+ LocallyConstant V.left M
  refine
    { toFun := fun f => ⟨f, (IsLocallyConstant.iff_continuous _).2 f.continuous⟩
      invFun := fun f => f.toContinuousMap
      left_inv := fun f => by ext; rfl
      right_inv := fun f => by ext; rfl
      map_add' := fun f g => by ext; rfl }

/-- The maps of the constant presheaf pull back locally constant functions. -/
lemma constantSections_map (S : Scheme.{u}) (M : AddCommGrpCat.{v})
    {V W : Over S} (a : W ⟶ V) (f : (constant S M).obj (op V)) (x : W.left) :
    constantSections S M W ((constant S M).map a.op f) x =
      constantSections S M V f (a.left x) := rfl

/-- Constant presheaves commute with restriction along every base morphism. -/
def restrictConstantIso (g : T ⟶ S) (M : AddCommGrpCat.{v}) :
    restrict g (constant S M) ≅ constant T M := Iso.refl _

/-- The actual abelian presheaf satisfies descent for the big relative étale topology. -/
def IsEtaleSheaf (F : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{v}) : Prop :=
  Presheaf.IsSheaf (topology S) F

/-- Sheafness is invariant under natural isomorphism. -/
lemma isEtaleSheaf_iff_of_iso {F G : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{v}} (e : F ≅ G) :
    IsEtaleSheaf F ↔ IsEtaleSheaf G :=
  Presheaf.isSheaf_of_iso_iff e

/-- Restriction along an arbitrary base morphism preserves étale sheaves. -/
lemma isEtaleSheaf_restrict (g : T ⟶ S) {F : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{v}}
    (hF : IsEtaleSheaf F) : IsEtaleSheaf (restrict g F) :=
  (Over.map g).op_comp_isSheaf_of_isSheaf (topology T) (topology S) F hF

/-- Locally constant functions to an abelian group satisfy étale descent. -/
lemma isEtaleSheaf_constant (S : Scheme.{u}) (M : AddCommGrpCat.{v}) :
    IsEtaleSheaf (constant S M) := by
  let : TopologicalSpace M := ⊥
  have : DiscreteTopology M := discreteTopology_bot M
  apply (Over.forget S).op_comp_isSheaf_of_isSheaf (topology S) Scheme.etaleTopology
  exact (isSheaf_fpqcTopology_continuousMapPresheafAb M).of_le
    (le_trans Scheme.etaleTopology_le_proetaleTopology
      Scheme.proetaleTopology_le_fpqcTopology)

/-- An étale sheaf with finitely generated constant models on an étale cover.
The coefficient groups may have torsion and may vary with the cover member. -/
def IsFinitelyGeneratedLocallyConstant
    (F : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{max u v}) : Prop :=
  IsEtaleSheaf F ∧
    ∃ (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S),
      ∀ i : 𝒰.I₀, ∃ M : AddCommGrpCat.{v}, AddGroup.FG M ∧
        Nonempty (restrict (𝒰.f i) F ≅ constant (𝒰.X i) M)

/-- A finitely generated constant presheaf is a local system. -/
lemma isFinitelyGeneratedLocallyConstant_constant (S : Scheme.{u})
    (M : AddCommGrpCat.{v}) [AddGroup.FG M] :
    IsFinitelyGeneratedLocallyConstant.{u, v} (constant S M) := by
  refine ⟨isEtaleSheaf_constant S M,
    ⟨Scheme.Cover.mkOfCovers (P := @Etale) PUnit (fun _ => S)
      (fun _ => 𝟙 S) (fun x => ⟨⟨⟩, x, rfl⟩) (fun _ => inferInstance), ?_⟩⟩
  intro i
  exact ⟨M, inferInstance, ⟨restrictConstantIso (𝟙 S) M⟩⟩

/-- Local systems are invariant under natural isomorphism of the actual presheaves. -/
lemma isFinitelyGeneratedLocallyConstant_iff_of_iso
    {F G : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{max u v}} (e : F ≅ G) :
    IsFinitelyGeneratedLocallyConstant F ↔ IsFinitelyGeneratedLocallyConstant G := by
  suffices ∀ {F G : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{max u v}}, (F ≅ G) →
      IsFinitelyGeneratedLocallyConstant F → IsFinitelyGeneratedLocallyConstant G from
    ⟨this e, this e.symm⟩
  intro F G e ⟨hF, 𝒰, h𝒰⟩
  refine ⟨(isEtaleSheaf_iff_of_iso e).1 hF, 𝒰, ?_⟩
  intro i
  obtain ⟨M, hM, ⟨a⟩⟩ := h𝒰 i
  exact ⟨M, hM, ⟨(restrictIso (𝒰.f i) e).symm ≪≫ a⟩⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- Local systems remain locally constant with finitely generated coefficients
under restriction along every base morphism. -/
lemma isFinitelyGeneratedLocallyConstant_restrict (g : T ⟶ S)
    {F : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{max u v}}
    (hF : IsFinitelyGeneratedLocallyConstant.{u, v} F) :
    IsFinitelyGeneratedLocallyConstant.{u, v} (restrict g F) := by
  obtain ⟨hF, 𝒰, h𝒰⟩ := hF
  refine ⟨isEtaleSheaf_restrict g hF, 𝒰.pullback₁ g, ?_⟩
  intro i
  obtain ⟨M, hM, ⟨e⟩⟩ := h𝒰 i
  refine ⟨M, hM, ⟨?_⟩⟩
  exact (restrictCompIso g ((𝒰.pullback₁ g).f i) F).symm ≪≫
    restrictCongrIso (𝒰.pullbackHom_map g i).symm F ≪≫
    restrictCompIso (𝒰.f i) (𝒰.pullbackHom g i) F ≪≫
    restrictIso (𝒰.pullbackHom g i) e ≪≫
    restrictConstantIso (𝒰.pullbackHom g i) M

end Langlands.AlgebraicGeometry.EtaleLocalSystem
