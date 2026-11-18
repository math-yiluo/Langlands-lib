import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Langlands.GroupScheme.RelativeIdentityComponent
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.Torus.MaximalAmbient
import Langlands.AbelianScheme.GroupSchemeSubalgebraDescentProof

/-! # Base-change reductions for extensions of groups of multiplicative type -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.ExtensionReduction

variable {S T : Scheme.{u}}

/-- The actual residue fibre after base change is the scalar extension
of the original residue fibre at the image point. -/
def residueFiberBaseChangeIso (b : T ⟶ S) (G : GroupScheme S) (t : T) :
    (baseChange (Spec.map (b.residueFieldMap t))).obj
        (RelativeIdentityComponent.residueFiber G (b t)) ≅
      RelativeIdentityComponent.residueFiber ((baseChange b).obj G) t :=
  Descent.pullbackComparison (S.fromSpecResidueField (b t))
      (Spec.map (b.residueFieldMap t)) (T.fromSpecResidueField t ≫ b)
      (b.SpecMap_residueFieldMap_fromSpecResidueField t) G ≪≫
    baseChangeCompIso b (T.fromSpecResidueField t) G

/-- Connectedness of residue fibres is preserved and reflected at points
above the base for finite-type group schemes. -/
theorem connectedSpace_residueFiber_baseChange_iff (b : T ⟶ S)
    (G : GroupScheme S) [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom] (t : T) :
    ConnectedSpace (RelativeIdentityComponent.residueFiber ((baseChange b).obj G) t).X.left ↔
      ConnectedSpace (RelativeIdentityComponent.residueFiber G (b t)).X.left := by
  let K := RelativeIdentityComponent.residueFiber G (b t)
  let c := Spec.map (b.residueFieldMap t)
  let : Algebra (S.residueField (b t)) (T.residueField t) :=
    (b.residueFieldMap t).hom.toAlgebra
  let e := (Over.forget _).mapIso
    ((Grp.forget _).mapIso (residueFiberBaseChangeIso b G t))
  have : LocallyOfFiniteType K.X.hom := by
    change LocallyOfFiniteType (pullback.snd _ _)
    infer_instance
  have : QuasiCompact K.X.hom := by
    change QuasiCompact (pullback.snd _ _)
    infer_instance
  constructor
  · intro hc
    have : ConnectedSpace ↥(pullback K.X.hom c : Scheme.{u}) :=
      (Scheme.homeoOfIso e).connectedSpace_iff.mpr hc
    have : Surjective c := (fieldExtension_fpqc
      (S.residueField (b t)) (T.residueField t)).1
    exact (pullback.fst K.X.hom c).surjective.connectedSpace
      (pullback.fst K.X.hom c).continuous
  · intro hc
    let := hc
    have : ConnectedSpace ((baseChange c).obj K).X.left :=
      K.connectedSpace_baseChange_of_connected c
    exact (Scheme.homeoOfIso e).connectedSpace_iff.mp this

/-- Commutativity of residue fibres is preserved and reflected at
points above the base, without a finiteness premise on the group. -/
theorem isCommMonObj_residueFiber_baseChange_iff (b : T ⟶ S)
    (G : GroupScheme S) (t : T) :
    IsCommMonObj (RelativeIdentityComponent.residueFiber ((baseChange b).obj G) t).X ↔
      IsCommMonObj (RelativeIdentityComponent.residueFiber G (b t)).X := by
  let K := RelativeIdentityComponent.residueFiber G (b t)
  let c := Spec.map (b.residueFieldMap t)
  let : Algebra (S.residueField (b t)) (T.residueField t) :=
    (b.residueFieldMap t).hom.toAlgebra
  let e : ((baseChange c).obj K).X ≅
      (RelativeIdentityComponent.residueFiber ((baseChange b).obj G) t).X :=
    (Grp.forget _).mapIso (residueFiberBaseChangeIso b G t)
  have : IsMonHom e.hom := by
    change IsMonHom (residueFiberBaseChangeIso b G t).hom.hom.hom
    infer_instance
  have : IsMonHom e.symm.hom := by
    change IsMonHom (residueFiberBaseChangeIso b G t).inv.hom.hom
    infer_instance
  constructor
  · intro hc
    let := hc
    have hK : IsCommMonObj ((baseChange c).obj K).X :=
      isCommMonObj_of_iso e.symm
    obtain ⟨hs, hf, hq⟩ := fieldExtension_fpqc
      (S.residueField (b t)) (T.residueField t)
    have : Surjective c := hs
    have : Flat c := hf
    have : QuasiCompact c := hq
    exact isCommMonObj_of_baseChange c K hK
  · intro hc
    let : IsCommMonObj K.X := hc
    have : IsCommMonObj ((baseChange c).obj K).X := inferInstance
    exact isCommMonObj_of_iso e

/-- The fibre alternative used in the extension theorem. -/
def ConnectedOrCommutativeFibers (G : GroupScheme S) : Prop :=
  ∀ s : S, ConnectedSpace (RelativeIdentityComponent.residueFiber G s).X.left ∨
    IsCommMonObj (RelativeIdentityComponent.residueFiber G s).X

/-- The extension theorem's mixed fibre condition survives arbitrary base change. -/
theorem ConnectedOrCommutativeFibers.baseChange {G : GroupScheme S}
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    (hG : ConnectedOrCommutativeFibers G) (b : T ⟶ S) :
    ConnectedOrCommutativeFibers ((baseChange b).obj G) := by
  intro t
  exact (or_congr (connectedSpace_residueFiber_baseChange_iff b G t)
    (isCommMonObj_residueFiber_baseChange_iff b G t)).mpr (hG (b t))

/-- Surjective base change also reflects the mixed fibre condition. -/
theorem connectedOrCommutativeFibers_baseChange_iff (b : T ⟶ S) [Surjective b]
    (G : GroupScheme S) [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom] :
    ConnectedOrCommutativeFibers ((baseChange b).obj G) ↔
      ConnectedOrCommutativeFibers G := by
  refine ⟨?_, fun h => h.baseChange b⟩
  intro h s
  obtain ⟨t, rfl⟩ := b.surjective s
  exact (or_congr (connectedSpace_residueFiber_baseChange_iff b G t)
    (isCommMonObj_residueFiber_baseChange_iff b G t)).mp (h t)

/-- A common diagonalizing fppf cover with affine members for two
groups of relative multiplicative type. -/
structure CommonAffineDiagonalizingCover (N Q : GroupScheme S) where
  cover : Scheme.Cover.{u} Scheme.fppfPrecoverage S
  affine : ∀ i, IsAffine (cover.X i)
  left_diagonalizable : ∀ i,
    RelativeMultiplicativeType.IsDiagonalizable ((baseChange (cover.f i)).obj N)
  right_diagonalizable : ∀ i,
    RelativeMultiplicativeType.IsDiagonalizable ((baseChange (cover.f i)).obj Q)

theorem nonempty_commonAffineDiagonalizingCover {N Q : GroupScheme S}
    (hN : RelativeMultiplicativeType.IsMultiplicativeType N)
    (hQ : RelativeMultiplicativeType.IsMultiplicativeType Q) :
    Nonempty (CommonAffineDiagonalizingCover N Q) := by
  classical
  obtain ⟨𝒰, h𝒰⟩ := hN
  have hV : ∀ i, RelativeMultiplicativeType.IsMultiplicativeType
      ((baseChange (𝒰.f i)).obj Q) := fun i => hQ.baseChange (𝒰.f i)
  choose 𝒱 h𝒱 using hV
  let 𝒞 := 𝒰.bind 𝒱
  have hN𝒞 : ∀ i, RelativeMultiplicativeType.IsDiagonalizable
      ((baseChange (𝒞.f i)).obj N) := by
    rintro ⟨i, j⟩
    exact RelativeMultiplicativeType.IsDiagonalizable.of_iso
      (baseChangeCompIso (𝒰.f i) ((𝒱 i).f j) N)
      ((h𝒰 i).baseChange ((𝒱 i).f j))
  have hQ𝒞 : ∀ i, RelativeMultiplicativeType.IsDiagonalizable
      ((baseChange (𝒞.f i)).obj Q) := by
    rintro ⟨i, j⟩
    exact RelativeMultiplicativeType.IsDiagonalizable.of_iso
      (baseChangeCompIso (𝒰.f i) ((𝒱 i).f j) Q) (h𝒱 i j)
  let 𝒜 (i : 𝒞.I₀) : Scheme.Cover.{u} Scheme.fppfPrecoverage (𝒞.X i) :=
    (𝒞.X i).affineCover.changeProp (fun j => by
      have := (𝒞.X i).affineCover.map_prop j
      exact ⟨inferInstance, inferInstance⟩)
  refine ⟨{
    cover := 𝒞.bind 𝒜
    affine := ?_
    left_diagonalizable := ?_
    right_diagonalizable := ?_ }⟩
  · rintro ⟨i, j⟩
    exact inferInstanceAs (IsAffine ((𝒞.X i).affineCover.X j))
  · rintro ⟨i, j⟩
    exact RelativeMultiplicativeType.IsDiagonalizable.of_iso
      (baseChangeCompIso (𝒞.f i) ((𝒜 i).f j) N)
      ((hN𝒞 i).baseChange ((𝒜 i).f j))
  · rintro ⟨i, j⟩
    exact RelativeMultiplicativeType.IsDiagonalizable.of_iso
      (baseChangeCompIso (𝒞.f i) ((𝒜 i).f j) Q)
      ((hQ𝒞 i).baseChange ((𝒜 i).f j))

/-- Choose a common affine diagonalizing fppf cover of the two endpoints. -/
def commonAffineDiagonalizingCover {N Q : GroupScheme S}
    (hN : RelativeMultiplicativeType.IsMultiplicativeType N)
    (hQ : RelativeMultiplicativeType.IsMultiplicativeType Q) :
    CommonAffineDiagonalizingCover N Q :=
  Classical.choice (nonempty_commonAffineDiagonalizingCover hN hQ)

end Langlands.GroupScheme.ExtensionReduction
