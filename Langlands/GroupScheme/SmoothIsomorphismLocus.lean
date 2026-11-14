import Langlands.GroupScheme.Lie.SmoothFibreRanks
import Langlands.GroupScheme.Torus.IsomorphismLocus
import Langlands.AlgebraicGeometry.FiberwiseOpenImmersion

/-! # Isomorphism neighbourhoods for smooth affine connected groups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.SmoothIsomorphismLocus

local instance smooth_baseChange {S T : Scheme.{u}} (b : T ⟶ S)
    (H : GroupScheme S) [Smooth H.X.hom] :
    Smooth ((baseChange b).obj H).X.hom :=
  inferInstanceAs (Smooth (pullback.snd H.X.hom b))

local instance affine_baseChange {S T : Scheme.{u}} (b : T ⟶ S)
    (H : GroupScheme S) [IsAffineHom H.X.hom] :
    IsAffineHom ((baseChange b).obj H).X.hom :=
  MorphismProperty.pullback_snd H.X.hom b inferInstance

local instance connected_baseChange {S T : Scheme.{u}} (b : T ⟶ S)
    (H : GroupScheme S) [GeometricallyConnected H.X.hom] :
    GeometricallyConnected ((baseChange b).obj H).X.hom :=
  inferInstanceAs (GeometricallyConnected (pullback.snd H.X.hom b))

local instance mono_baseChange {S T : Scheme.{u}} (b : T ⟶ S)
    {H G : GroupScheme S} (i : H ⟶ G) [Mono i.hom.hom] :
    Mono ((baseChange b).map i).hom.hom :=
  inferInstanceAs (Mono ((Over.pullback b).map i.hom.hom))

/-- A fibrewise isomorphism from a flat finitely presented family to a locally
finite type family is an isomorphism. -/
theorem isIso_of_residueField_fibres
    {B : Scheme.{u}} {X Y : Over B} (f : X ⟶ Y)
    [Flat X.hom] [LocallyOfFinitePresentation X.hom] [LocallyOfFiniteType Y.hom]
    (hf : ∀ s : B, IsIso ((Over.pullback (B.fromSpecResidueField s)).map f)) :
    IsIso f := by
  have : IsOpenImmersion f.left :=
    Langlands.AlgebraicGeometry.isOpenImmersion_of_fiberwise f fun s => by
      let := hf s
      exact inferInstanceAs
        (IsOpenImmersion (((Over.forget _).map
          ((Over.pullback (B.fromSpecResidueField s)).map f))))
  have : Surjective f.left := by
    refine ⟨fun y => ?_⟩
    let s : B := Y.hom y
    obtain ⟨y', hy', -⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := Y.hom) (g := B.fromSpecResidueField s) y
      (IsLocalRing.closedPoint (B.residueField s))
      (Scheme.fromSpecResidueField_apply _ _).symm
    let := hf s
    have : IsIso ((Over.pullback (B.fromSpecResidueField s)).map f).left :=
      Functor.map_isIso (Over.forget (Spec (B.residueField s)))
        ((Over.pullback (B.fromSpecResidueField s)).map f)
    obtain ⟨x', hx'⟩ :=
      (((Over.pullback (B.fromSpecResidueField s)).map f).left).surjective y'
    have hcomp : pullback.fst X.hom (B.fromSpecResidueField s) ≫ f.left =
        ((Over.pullback (B.fromSpecResidueField s)).map f).left ≫
          pullback.fst Y.hom (B.fromSpecResidueField s) :=
      (pullback.lift_fst _ _ _).symm
    refine ⟨pullback.fst X.hom (B.fromSpecResidueField s) x', ?_⟩
    rw [← hy', ← hx']
    change (pullback.fst X.hom (B.fromSpecResidueField s) ≫ f.left) x' =
      (((Over.pullback (B.fromSpecResidueField s)).map f).left ≫
        pullback.fst Y.hom (B.fromSpecResidueField s)) x'
    exact congrArg (fun a => a x') hcomp
  have : IsIso f.left :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩
  have : IsIso ((Over.forget B).map f) := ‹IsIso f.left›
  exact isIso_of_reflects_iso f (Over.forget B)

/-- The fibrewise criterion in the actual group-scheme category. -/
theorem isIso_of_group_residueField_fibres
    {S : Scheme.{u}} {H G : GroupScheme S} (i : H ⟶ G)
    [Smooth H.X.hom] [LocallyOfFiniteType G.X.hom]
    (hi : ∀ s : S, IsIso ((baseChange (S.fromSpecResidueField s)).map i)) :
    IsIso i := by
  have : IsIso i.hom.hom := isIso_of_residueField_fibres i.hom.hom fun s => by
    have := hi s
    exact Functor.map_isIso (Grp.forget _) ((baseChange (S.fromSpecResidueField s)).map i)
  exact TorusIsomorphismLocus.isIso_of_underlying i

section Affine

variable {R : CommRingCat.{u}} {H G : GroupScheme (Spec R)}
  [Smooth H.X.hom] [IsAffineHom H.X.hom] [GeometricallyConnected H.X.hom]
  [Smooth G.X.hom] [IsAffineHom G.X.hom] [GeometricallyConnected G.X.hom]

/-- Lie dimension at any actual field-valued point is its relative Lie rank. -/
theorem dimension_fieldPoint (G : GroupScheme (Spec R))
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (K : Type u) [Field K] (x : Spec (CommRingCat.of K) ⟶ Spec R) :
    Lie.dimension ((baseChange x).obj G) =
      Module.rankAtStalk (R := R) (Additive (lieKernel G R))
        (x (IsLocalRing.closedPoint K)) := by
  obtain ⟨f, rfl⟩ := Spec.homEquiv.symm.surjective x
  let : Algebra R K := f.hom.toAlgebra
  exact Lie.dimension_baseChange_eq_rankAtStalk G K

/-- A field-valued isomorphism of smooth affine groups with geometrically
connected fibres extends to a base open neighbourhood, for a monic map. -/
theorem exists_open_affine (i : H ⟶ G) [Mono i.hom.hom]
    (K : Type u) [Field K] (x : Spec (CommRingCat.of K) ⟶ Spec R)
    (hx : IsIso ((baseChange x).map i)) :
    ∃ (V : Scheme.{u}) (q : V ⟶ Spec R), IsOpenImmersion q ∧
      ∃ bx : Spec (CommRingCat.of K) ⟶ V, bx ≫ q = x ∧
        IsIso ((baseChange q).map i) := by
  let p := x (IsLocalRing.closedPoint K)
  let rH := Module.rankAtStalk (R := R) (Additive (lieKernel H R))
  let rG := Module.rankAtStalk (R := R) (Additive (lieKernel G R))
  have heq : rH p = rG p := by
    change Module.rankAtStalk (R := R) (Additive (lieKernel H R))
      (x (IsLocalRing.closedPoint K)) =
        Module.rankAtStalk (R := R) (Additive (lieKernel G R))
          (x (IsLocalRing.closedPoint K))
    rw [← dimension_fieldPoint H K x, ← dimension_fieldPoint G K x]
    let := hx
    exact Lie.dimension_eq_of_iso (asIso ((baseChange x).map i))
  let U : (Spec R).Opens :=
    ⟨{s | rH s = rH p} ∩ {s | rG s = rG p},
      (Lie.isLocallyConstant_lieRank H).isOpen_fiber _ |>.inter
        ((Lie.isLocallyConstant_lieRank G).isOpen_fiber _)⟩
  have hpx : Set.range x ⊆ U := by
    rintro _ ⟨z, rfl⟩
    have hz : z = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    subst z
    exact ⟨rfl, rfl⟩
  let bx : Spec (CommRingCat.of K) ⟶ U :=
    IsOpenImmersion.lift U.ι x (by simpa using hpx)
  refine ⟨U, U.ι, inferInstance, bx, IsOpenImmersion.lift_fac _ _ _, ?_⟩
  apply isIso_of_group_residueField_fibres
  intro s
  let b := (U : Scheme).fromSpecResidueField s
  have hb : (b ≫ U.ι) (IsLocalRing.closedPoint ((U : Scheme).residueField s)) = U.ι s := by
    change U.ι (b (IsLocalRing.closedPoint ((U : Scheme).residueField s))) = U.ι s
    rw [Scheme.fromSpecResidueField_apply]
  have hdim : Lie.dimension ((baseChange (b ≫ U.ι)).obj H) =
      Lie.dimension ((baseChange (b ≫ U.ι)).obj G) := by
    calc
      _ = rH ((b ≫ U.ι)
          (IsLocalRing.closedPoint ((U : Scheme).residueField s))) :=
        dimension_fieldPoint H ((U : Scheme).residueField s) (b ≫ U.ι)
      _ = rH (U.ι s) := congrArg rH hb
      _ = rG (U.ι s) := s.2.1.trans (heq.trans s.2.2.symm)
      _ = rG ((b ≫ U.ι)
          (IsLocalRing.closedPoint ((U : Scheme).residueField s))) :=
        congrArg rG hb.symm
      _ = _ := (dimension_fieldPoint G ((U : Scheme).residueField s) (b ≫ U.ι)).symm
  have hHc : ConnectedSpace ((baseChange (b ≫ U.ι)).obj H).X.left :=
    pullback_of_geometrically
      (GeometricallyConnected.geometrically_connectedSpace (f := H.X.hom)) _ _
  have hGc : ConnectedSpace ((baseChange (b ≫ U.ι)).obj G).X.left :=
    pullback_of_geometrically
      (GeometricallyConnected.geometrically_connectedSpace (f := G.X.hom)) _ _
  have : IsIso ((baseChange (b ≫ U.ι)).map i) :=
    Lie.isIso_of_mono_of_dimension_eq _ hdim
  exact (TorusIsomorphismLocus.isIso_comp_baseChange_iff U.ι b i).mp this

end Affine

/-- A field-valued isomorphism of smooth affine families with geometrically
connected fibres extends to an open neighbourhood for a monic homomorphism. -/
theorem exists_open {S : Scheme.{u}} {H G : GroupScheme S}
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [GeometricallyConnected H.X.hom]
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [GeometricallyConnected G.X.hom]
    (i : H ⟶ G) [Mono i.hom.hom]
    (K : Type u) [Field K] (x : Spec (CommRingCat.of K) ⟶ S)
    (hx : IsIso ((baseChange x).map i)) :
    ∃ (V : Scheme.{u}) (q : V ⟶ S), IsOpenImmersion q ∧
      ∃ bx : Spec (CommRingCat.of K) ⟶ V, bx ≫ q = x ∧
        IsIso ((baseChange q).map i) := by
  let C := TorusClosedImmersionLocus.fieldPointAffineChart x
  let hp : IsOpenImmersion C.map := C.isOpen
  have hcx : IsIso ((baseChange (C.lift ≫ C.map)).map i) := by
    rw [C.fac]
    exact hx
  have hxi := (TorusIsomorphismLocus.isIso_comp_baseChange_iff C.map C.lift i).mp hcx
  obtain ⟨V, q, hq, bx, hbx, hi⟩ :=
    exists_open_affine ((baseChange C.map).map i) K C.lift hxi
  let := hq
  refine ⟨V, q ≫ C.map, inferInstance, bx, ?_, ?_⟩
  · rw [← Category.assoc, hbx]
    exact C.fac
  · exact (TorusIsomorphismLocus.isIso_comp_baseChange_iff C.map q i).mpr hi

/-- The local comparison statement for smooth affine families over any base. -/
def OpenIsomorphismStatement : Prop :=
  ∀ (S : Scheme.{u}) (H G : GroupScheme S)
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [GeometricallyConnected H.X.hom]
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [GeometricallyConnected G.X.hom]
    (i : H ⟶ G) [Mono i.hom.hom]
    (K : Type u) [Field K] (x : Spec (CommRingCat.of K) ⟶ S),
    IsIso ((baseChange x).map i) →
    ∃ (V : Scheme.{u}) (q : V ⟶ S), IsOpenImmersion q ∧
      ∃ bx : Spec (CommRingCat.of K) ⟶ V, bx ≫ q = x ∧
        IsIso ((baseChange q).map i)

/-- The comparison is unconditional, including over nonreduced bases. -/
theorem openIsomorphism : OpenIsomorphismStatement.{u} := by
  intro S H G _ _ _ _ _ _ i _ K _ x hx
  exact exists_open i K x hx

end Langlands.GroupScheme.SmoothIsomorphismLocus
