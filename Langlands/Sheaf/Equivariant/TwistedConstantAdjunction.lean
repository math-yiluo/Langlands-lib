import Langlands.Sheaf.Equivariant.TwistedExactGlobalComparison
import Langlands.Sheaf.Equivariant.LocalActionConstant
import Langlands.Sheaf.Equivariant.LocalActionSmoothConstant
import Langlands.Representation.Category.SmoothPartAdjunction
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.CategoryTheory.Adjunction.Restrict

/-!
# Constant equivariant sheaves on the twisted site and injectivity of global sections

Let `G` act on an object `X` and let `J` be a translation-invariant topology on the site over
`X`. A representation `M` of `G` gives a presheaf of modules on the twisted category that is
`M` on every object, where a twisted morphism with twist `g` acts by `g⁻¹`. Maps from this
presheaf to a module presheaf `F` are the `G`-equivariant maps from `M` to the sections of `F`
over the base object, with the action of `TwistedGlobalSections`. Sheafifying gives the
constant equivariant sheaf of `M`, left adjoint to the global sections representation. For a
smooth representation and a local action system whose admissible actions are lifts, the
constant sheaf is discrete, and locally discrete, so the constant sheaf functor is left
adjoint to Berkovich's `Γ_{X{G}}` on discrete and on locally discrete sheaves. These left
adjoints preserve monomorphisms, so `Γ_{X{G}}` sends injective objects to injective smooth
representations: the input of the composite-functor spectral sequence
`H^p(G, H^q(X{G}, F)) ⟹ H^{p+q}(X(G), F)` of Berkovich's §1.2.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant.TwistedOver

open CategoryTheory CategoryTheory.Limits Opposite
open Langlands.Sheaf.Equivariant

universe w u v uG

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C} {X : C}
variable {G : Type uG} [Group G] {ρ : G →* Aut X}

section Base

variable [P.ContainsIdentities]

/-- The twisted morphism from an object to the base object with twist `1`: its structure
map. -/
def toBase (U : TwistedOver P ρ) : U ⟶ base P ρ :=
  homMk 1 (TwistedOver.hom U) (by rw [rho_one_hom]; rfl)

@[simp]
theorem toBase_twist (U : TwistedOver P ρ) : Hom.twist (toBase U) = 1 := rfl

@[simp]
theorem toBase_left (U : TwistedOver P ρ) : Hom.left (toBase U) = TwistedOver.hom U := rfl

/-- The structure map of the base object is its identity. -/
theorem toBase_base : toBase (base P ρ) = 𝟙 (base P ρ) :=
  hom_ext rfl rfl

/-- A twisted morphism with twist `g`, followed by the structure map, is the structure map
followed by the action of `g` on the base. -/
theorem comp_toBase {U V : TwistedOver P ρ} (f : V ⟶ U) :
    f ≫ toBase U = toBase V ≫ baseEndo (Hom.twist f) :=
  hom_ext (by simp) (by simpa using f.w)

end Base

section Presheaf

variable (R : Type w) [CommRing R]
variable (P ρ)

/-- A representation `M` of `G` as a constant presheaf of modules on the twisted category: it
is `M` on every object, and a twisted morphism with twist `g` acts by `g⁻¹`. -/
def constantTwisted : Rep.{w} R G ⥤ (TwistedOver P ρ)ᵒᵖ ⥤ ModuleCat.{w} R where
  obj M :=
    { obj _ := ModuleCat.of R M
      map f := ModuleCat.ofHom (M.ρ (Hom.twist f.unop)⁻¹)
      map_id _ := by
        ext m
        change M.ρ (1 : G)⁻¹ m = m
        simp
      map_comp f g := by
        ext m
        change M.ρ (Hom.twist f.unop * Hom.twist g.unop)⁻¹ m =
          M.ρ (Hom.twist g.unop)⁻¹ (M.ρ (Hom.twist f.unop)⁻¹ m)
        simp [mul_inv_rev, map_mul, Module.End.mul_apply] }
  map a :=
    { app _ := ModuleCat.ofHom a.hom.toLinearMap
      naturality _ _ f := by
        ext m
        exact Rep.hom_comm_apply a (Hom.twist f.unop)⁻¹ m }

variable {P ρ}

@[simp]
theorem constantTwisted_obj_map_apply (M : Rep.{w} R G) {U V : (TwistedOver P ρ)ᵒᵖ} (f : U ⟶ V)
    (m : M) : ((constantTwisted P ρ R).obj M).map f m = M.ρ (Hom.twist f.unop)⁻¹ m :=
  rfl

variable [P.ContainsIdentities]

/-- Restrict an equivariant map into the sections over the base object to every object, along
the structure maps. -/
def constantTwistedLift (M : Rep.{w} R G) (F : (TwistedOver P ρ)ᵒᵖ ⥤ ModuleCat.{w} R)
    (a : M ⟶ (sectionsRep R (baseAction P ρ)).obj F) :
    (constantTwisted P ρ R).obj M ⟶ F where
  app U := ModuleCat.ofHom a.hom.toLinearMap ≫ F.map (toBase U.unop).op
  naturality U V f := by
    ext m
    change (F.map (toBase V.unop).op).hom (a.hom (M.ρ (Hom.twist f.unop)⁻¹ m)) =
      (F.map f).hom ((F.map (toBase U.unop).op).hom (a.hom m))
    have h := Rep.hom_comm_apply a (Hom.twist f.unop)⁻¹ m
    change a.hom (M.ρ _ m) =
      (F.map (baseEndo ((Hom.twist f.unop)⁻¹)⁻¹).op).hom (a.hom m) at h
    rw [inv_inv] at h
    rw [h]
    have e : (baseEndo (Hom.twist f.unop)).op ≫ (toBase V.unop).op = (toBase U.unop).op ≫ f := by
      apply Quiver.Hom.unop_inj
      exact (comp_toBase f.unop).symm
    have := congrArg (fun k => (F.map k).hom (a.hom m)) e
    simp only [Functor.map_comp, ModuleCat.hom_comp] at this
    exact this

/-- Maps out of the constant twisted presheaf are the equivariant maps into the sections over
the base object. -/
def constantTwistedHomEquiv (M : Rep.{w} R G) (F : (TwistedOver P ρ)ᵒᵖ ⥤ ModuleCat.{w} R) :
    ((constantTwisted P ρ R).obj M ⟶ F) ≃
      (M ⟶ (sectionsRep R (baseAction P ρ)).obj F) where
  toFun a := Rep.ofHom
    { toLinearMap := (a.app (op (base P ρ))).hom
      isIntertwining' g := by
        ext m
        have h := ConcreteCategory.congr_hom (a.naturality (baseEndo (P := P) (ρ := ρ) g⁻¹).op) m
        change (a.app (op (base P ρ))).hom (M.ρ (Hom.twist (baseEndo (P := P) (ρ := ρ) g⁻¹))⁻¹ m) =
          (F.map (baseEndo (P := P) (ρ := ρ) g⁻¹).op).hom ((a.app (op (base P ρ))).hom m) at h
        rw [baseEndo_twist, inv_inv] at h
        exact h }
  invFun := constantTwistedLift R M F
  left_inv a := by
    apply NatTrans.ext
    funext U
    ext m
    have h := ConcreteCategory.congr_hom (a.naturality (toBase U.unop).op) m
    change (a.app U).hom (M.ρ (Hom.twist (toBase U.unop))⁻¹ m) =
      (F.map (toBase U.unop).op).hom ((a.app (op (base P ρ))).hom m) at h
    rw [toBase_twist, inv_one, map_one] at h
    change (a.app U).hom m = _ at h
    change (F.map (toBase U.unop).op).hom ((a.app (op (base P ρ))).hom m) = (a.app U).hom m
    exact h.symm
  right_inv a := by
    ext m
    change F.map (toBase (base P ρ)).op (a.hom m) = a.hom m
    rw [toBase_base, op_id, F.map_id]
    rfl

/-- The constant twisted presheaf functor is left adjoint to the sections over the base object
as a representation of `G`. -/
def constantTwistedAdjunction :
    constantTwisted P ρ R ⊣ sectionsRep R (baseAction P ρ) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := constantTwistedHomEquiv R
      homEquiv_naturality_left_symm := by
        intro M N F a b
        ext U m
        rfl
      homEquiv_naturality_right := by
        intro M F F' a b
        ext m
        rfl }

omit [P.ContainsIdentities] in
instance constantTwisted_preservesMonomorphisms :
    (constantTwisted P ρ R).PreservesMonomorphisms where
  preserves {M N} a _ := by
    have : ∀ U, Mono (((constantTwisted P ρ R).map a).app U) := fun U => by
      change Mono ((forget₂ (Rep.{w} R G) (ModuleCat.{w} R)).map a)
      infer_instance
    exact NatTrans.mono_of_mono_app _

end Presheaf

section Sheaf

variable [P.RespectsIso] [P.ContainsIdentities]
variable (J : GrothendieckTopology (P.Over ⊤ X)) [IsTranslationInvariant (ρ := ρ) J]
variable (R : Type w) [CommRing R]
variable [HasSheafify (twistedTopology ρ J) (ModuleCat.{w} R)]

/-- The constant equivariant sheaf of a representation: the sheafification of the constant
twisted presheaf. -/
def constantTwistedSheaf : Rep.{w} R G ⥤ Sheaf (twistedTopology ρ J) (ModuleCat.{w} R) :=
  constantTwisted P ρ R ⋙ presheafToSheaf (twistedTopology ρ J) (ModuleCat.{w} R)

/-- The constant equivariant sheaf functor is left adjoint to the global sections
representation. -/
def constantTwistedSheafAdjunction :
    constantTwistedSheaf J R ⊣ sheafGlobalSectionsRep J R (ρ := ρ) :=
  (constantTwistedAdjunction R).comp
    (sheafificationAdjunction (twistedTopology ρ J) (ModuleCat.{w} R))

instance constantTwistedSheaf_preservesMonomorphisms :
    (constantTwistedSheaf J R (ρ := ρ)).PreservesMonomorphisms := by
  dsimp [constantTwistedSheaf]
  infer_instance

/-- Global sections send injective module sheaves on the twisted site to injective
representations. -/
instance sheafGlobalSectionsRep_preservesInjectiveObjects :
    (sheafGlobalSectionsRep J R (ρ := ρ)).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (constantTwistedSheafAdjunction J R)

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- The constant equivariant sheaf of a smooth representation. -/
def smoothConstantTwistedSheaf :
    SmoothRep.{w, uG, w} R G ⥤ Sheaf (twistedTopology ρ J) (ModuleCat.{w} R) :=
  SmoothRep.toRep ⋙ constantTwistedSheaf J R

/-- The constant equivariant sheaf functor on smooth representations is left adjoint to
Berkovich's `Γ_{X{G}}` on all module sheaves on the twisted site. -/
def smoothConstantTwistedSheafAdjunction :
    smoothConstantTwistedSheaf J R ⊣ sheafGlobalSectionsSmooth J R (ρ := ρ) :=
  (SmoothRep.toRepSmoothPartAdjunction R G).comp (constantTwistedSheafAdjunction J R)

instance smoothConstantTwistedSheaf_preservesMonomorphisms :
    (smoothConstantTwistedSheaf J R (ρ := ρ)).PreservesMonomorphisms := by
  dsimp [smoothConstantTwistedSheaf]
  infer_instance

/-- `Γ_{X{G}}` sends injective module sheaves on the twisted site to injective smooth
representations. -/
instance sheafGlobalSectionsSmooth_preservesInjectiveObjects :
    (sheafGlobalSectionsSmooth J R (ρ := ρ)).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (smoothConstantTwistedSheafAdjunction J R)

end Sheaf

section Lift

variable (R : Type w) [CommRing R] [TopologicalSpace G]
variable (L : LocalActionSystem (TwistedOver P ρ) G)

/-- For a local action system whose admissible actions are lifts, the constant twisted
presheaf of a smooth representation is discrete: an admissible action of `H` acts on its
sections through the representation, and every vector is fixed by an open subgroup. -/
theorem isDiscrete_constantTwisted (hL : L.IsLiftSystem) (M : SmoothRep.{w, uG, w} R G) :
    L.IsDiscrete ((constantTwisted P ρ R).obj (SmoothRep.toRep.obj M)) := by
  intro U H a ha m
  obtain ⟨K, hK⟩ := M.isSmooth m
  refine ⟨H ⊓ K, inf_le_left, fun h hh => ?_⟩
  have hhK : (h : G) ∈ K := hh.2
  change M.representation (Hom.twist (a h).unop)⁻¹ m = m
  rw [hL U H a ha h, inv_inv]
  exact (Representation.mem_invariants _ _).mp hK ⟨h, hhK⟩

end Lift

section Discrete

variable [P.RespectsIso] [P.ContainsIdentities]
variable (J : GrothendieckTopology (P.Over ⊤ X)) [IsTranslationInvariant (ρ := ρ) J]
variable (R : Type w) [CommRing R]
variable [HasSheafify (twistedTopology ρ J) (ModuleCat.{w} R)]
variable [TopologicalSpace G] [IsTopologicalGroup G]
variable (L : LocalActionSystem (TwistedOver P ρ) G)
variable [L.HasFiniteEquivariantRefinements (twistedTopology ρ J)]

omit [P.ContainsIdentities] [IsTopologicalGroup G] in
/-- The constant equivariant sheaf of a smooth representation is discrete. -/
theorem discreteSheafProperty_smoothConstantTwistedSheaf (hL : L.IsLiftSystem)
    (M : SmoothRep.{w, uG, w} R G) :
    L.discreteSheafProperty (ModuleCat.{w} R) (twistedTopology ρ J)
      ((smoothConstantTwistedSheaf J R).obj M) :=
  isDiscrete_sheafify (isDiscrete_constantTwisted R L hL M)

/-- The constant equivariant sheaf functor on smooth representations, with values in discrete
sheaves. -/
def discreteConstantTwisted (hL : L.IsLiftSystem) :
    SmoothRep.{w, uG, w} R G ⥤ L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J) :=
  (L.discreteSheafProperty (ModuleCat.{w} R) (twistedTopology ρ J)).lift
    (smoothConstantTwistedSheaf J R) (discreteSheafProperty_smoothConstantTwistedSheaf J R L hL)

omit [P.ContainsIdentities] [IsTopologicalGroup G] in
/-- Followed by the inclusion, the discrete constant functor is the constant equivariant sheaf
functor. -/
theorem discreteConstantTwisted_comp_inclusion (hL : L.IsLiftSystem) :
    discreteConstantTwisted J R L hL ⋙
        L.discreteSheafInclusion (ModuleCat.{w} R) (twistedTopology ρ J) =
      smoothConstantTwistedSheaf J R :=
  rfl

/-- The discrete constant functor is left adjoint to Berkovich's `Γ_{X{G}}` on discrete
sheaves. -/
def discreteConstantTwistedAdjunction (hL : L.IsLiftSystem) :
    discreteConstantTwisted J R L hL ⊣ discreteGlobalSections J R L :=
  (smoothConstantTwistedSheafAdjunction J R).restrictFullyFaithful
    (iC := 𝟭 _) (iD := L.discreteSheafInclusion (ModuleCat.{w} R) (twistedTopology ρ J))
    (Functor.FullyFaithful.id _) (Functor.FullyFaithful.ofFullyFaithful _)
    (Iso.refl _) (Iso.refl _)

omit [P.ContainsIdentities] [IsTopologicalGroup G] in
/-- The discrete constant functor preserves monomorphisms. -/
theorem discreteConstantTwisted_preservesMonomorphisms (hL : L.IsLiftSystem) :
    (discreteConstantTwisted J R L hL).PreservesMonomorphisms where
  preserves f _ := by
    have : Mono ((L.discreteSheafInclusion (ModuleCat.{w} R) (twistedTopology ρ J)).map
        ((discreteConstantTwisted J R L hL).map f)) :=
      (inferInstance : Mono ((smoothConstantTwistedSheaf J R).map f))
    exact (L.discreteSheafInclusion (ModuleCat.{w} R) (twistedTopology ρ J)).mono_of_mono_map this

/-- `Γ_{X{G}}` sends injective discrete sheaves to injective smooth representations. -/
theorem discreteGlobalSections_preservesInjectiveObjects (hL : L.IsLiftSystem) :
    (discreteGlobalSections J R L).PreservesInjectiveObjects :=
  haveI := discreteConstantTwisted_preservesMonomorphisms J R L hL
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (discreteConstantTwistedAdjunction J R L hL)

end Discrete

section LocallyDiscrete

variable [P.RespectsIso] [P.ContainsIdentities]
variable (J : GrothendieckTopology (P.Over ⊤ X)) [IsTranslationInvariant (ρ := ρ) J]
variable (R : Type w) [CommRing R]
variable [HasSheafify (twistedTopology ρ J) (ModuleCat.{w} R)]
variable [TopologicalSpace G] [IsTopologicalGroup G]
variable (L : LocalActionSystem (TwistedOver P ρ) G)
variable [L.HasAdmissibleRefinements (twistedTopology ρ J)]

omit [P.ContainsIdentities] [IsTopologicalGroup G] in
/-- The constant equivariant sheaf of a smooth representation is locally discrete. -/
theorem smoothSheafProperty_smoothConstantTwistedSheaf (hL : L.IsLiftSystem)
    (M : SmoothRep.{w, uG, w} R G) :
    L.smoothSheafProperty (ModuleCat.{w} R) (twistedTopology ρ J)
      ((smoothConstantTwistedSheaf J R).obj M) :=
  -- The universes are given explicitly: elaboration otherwise fails to solve a universe
  -- constraint for the morphism universe of the twisted category.
  LocalActionSystem.isLocallyDiscrete_sheafify.{max v uG, max u v, uG, w, w} L
    (twistedTopology ρ J)
    (LocalActionSystem.IsDiscrete.isLocallyDiscrete L
      (LocalActionSystem.HasAdmissibleRefinements.covers (L := L) (J := twistedTopology ρ J))
      (isDiscrete_constantTwisted R L hL M))

/-- The constant equivariant sheaf functor on smooth representations, with values in locally
discrete sheaves. -/
def smoothSheafConstantTwisted (hL : L.IsLiftSystem) :
    SmoothRep.{w, uG, w} R G ⥤ L.SmoothSheaf (ModuleCat.{w} R) (twistedTopology ρ J) :=
  (L.smoothSheafProperty (ModuleCat.{w} R) (twistedTopology ρ J)).lift
    (smoothConstantTwistedSheaf J R) (smoothSheafProperty_smoothConstantTwistedSheaf J R L hL)

omit [P.ContainsIdentities] [IsTopologicalGroup G] in
/-- Followed by the inclusion, the locally discrete constant functor is the constant
equivariant sheaf functor. -/
theorem smoothSheafConstantTwisted_comp_inclusion (hL : L.IsLiftSystem) :
    smoothSheafConstantTwisted J R L hL ⋙
        L.smoothSheafInclusion (ModuleCat.{w} R) (twistedTopology ρ J) =
      smoothConstantTwistedSheaf J R :=
  rfl

/-- The locally discrete constant functor is left adjoint to Berkovich's `Γ_{X{G}}` on
locally discrete sheaves. -/
def smoothSheafConstantTwistedAdjunction (hL : L.IsLiftSystem) :
    smoothSheafConstantTwisted J R L hL ⊣
      exactGlobalSections J R (L.smoothSheafInclusion (ModuleCat.{w} R) (twistedTopology ρ J)) :=
  (smoothConstantTwistedSheafAdjunction J R).restrictFullyFaithful
    (iC := 𝟭 _) (iD := L.smoothSheafInclusion (ModuleCat.{w} R) (twistedTopology ρ J))
    (Functor.FullyFaithful.id _) (Functor.FullyFaithful.ofFullyFaithful _)
    (Iso.refl _) (Iso.refl _)

omit [P.ContainsIdentities] [IsTopologicalGroup G] in
/-- The locally discrete constant functor preserves monomorphisms. -/
theorem smoothSheafConstantTwisted_preservesMonomorphisms (hL : L.IsLiftSystem) :
    (smoothSheafConstantTwisted J R L hL).PreservesMonomorphisms where
  preserves f _ := by
    have : Mono ((L.smoothSheafInclusion (ModuleCat.{w} R) (twistedTopology ρ J)).map
        ((smoothSheafConstantTwisted J R L hL).map f)) :=
      (inferInstance : Mono ((smoothConstantTwistedSheaf J R).map f))
    exact (L.smoothSheafInclusion (ModuleCat.{w} R) (twistedTopology ρ J)).mono_of_mono_map this

/-- `Γ_{X{G}}` sends injective locally discrete sheaves to injective smooth
representations. -/
theorem exactGlobalSections_smoothSheafInclusion_preservesInjectiveObjects
    (hL : L.IsLiftSystem) :
    (exactGlobalSections J R
      (L.smoothSheafInclusion (ModuleCat.{w} R) (twistedTopology ρ J))).PreservesInjectiveObjects :=
  haveI := smoothSheafConstantTwisted_preservesMonomorphisms J R L hL
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (smoothSheafConstantTwistedAdjunction J R L hL)

end LocallyDiscrete

end Langlands.Sheaf.Equivariant.TwistedOver
