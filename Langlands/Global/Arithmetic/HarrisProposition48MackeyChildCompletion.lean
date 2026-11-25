import Langlands.Global.Arithmetic.HarrisProposition48MackeyChildFields
import Langlands.Weil.Local.IntermediateWeil

/-! # The completed fields and compatible place datum of a raw Mackey child -/

noncomputable section

universe uF

namespace Langlands.Global.Harris.MackeyChild

open NumberField AdelicFunctoriality LocalClassField LocalFactor.CommonClosure
open GeneralPosition Weil.Local ClassFieldTheory.Global
open IsDedekindDomain.HeightOneSpectrum
open scoped NumberField FiniteExtension

variable (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L)
  (T : Extension Q.F)

local notation "w" => Q.Ps.vTilde

instance top_liesOver_basePlace : (w).asIdeal.LiesOver (basePlace Q D).asIdeal := by
  change (w).asIdeal.LiesOver ((w).asIdeal.under (𝓞 D))
  infer_instance

/-- Identify the actual completed base `D` with its stage of the parent tower. -/
structure CompletedBase where
  iso : FiniteCompletion D (basePlace Q D) ≃+* T.field
  commutes : ∀ x,
    ((iso x : T.field) : AlgebraicClosure Q.F.Carrier) =
      Q.Ps.isoTilde (FiniteExtension.completionMap (basePlace Q D) w x)

namespace CompletedBase

/-- The equality of the two embedded fields gives their commuting identification. -/
def of_tower (hT : T.field ≤ (galoisClosure Q.F Q.F').field)
    (hD : ∀ x : FiniteCompletion Q.L w,
    x ∈ MackeyCompletion.completedField Q.Ps.v w D ↔
      (Q.Ps.isoTilde x : AlgebraicClosure Q.F.Carrier) ∈ T.field) :
    CompletedBase Q D T := by
  let f := (galoisClosure Q.F Q.F').field.val.toRingHom.comp
    (Q.Ps.isoTilde.toRingHom.comp (FiniteExtension.completionMap (basePlace Q D) w))
  let g := f.codRestrict T.field fun x =>
    (hD _).mp ((MackeyCompletion.mem_image_iff Q.Ps.v (basePlace Q D) w _).mpr ⟨x, rfl⟩)
  refine ⟨RingEquiv.ofBijective g ⟨g.injective, ?_⟩, fun _ => rfl⟩
  intro x
  let y : (galoisClosure Q.F Q.F').field := ⟨x, hT x.2⟩
  obtain ⟨z, hz⟩ := Q.Ps.isoTilde.surjective y
  have hz' : (Q.Ps.isoTilde z : AlgebraicClosure Q.F.Carrier) = x := congrArg Subtype.val hz
  obtain ⟨a, ha⟩ := (MackeyCompletion.mem_image_iff Q.Ps.v (basePlace Q D) w z).mp
    ((hD z).mpr (hz'.symm ▸ x.2))
  exact ⟨a, Subtype.ext ((congrArg (fun b => (Q.Ps.isoTilde b : AlgebraicClosure Q.F.Carrier))
    ha).trans hz')⟩

/-- Embed the actual parent completion into the algebraic closure of the child base. -/
def topEmbedding : FiniteCompletion Q.L w →+* AlgebraicClosure T.field :=
  (intermediateClosureEquiv Q.F T).symm.toRingEquiv.toRingHom.comp
    ((galoisClosure Q.F Q.F').field.val.toRingHom.comp Q.Ps.isoTilde.toRingHom)

variable {Q D T} (A : CompletedBase Q D T)

theorem topEmbedding_commutes (x : FiniteCompletion D (basePlace Q D)) :
    topEmbedding Q T (algebraMap (FiniteCompletion D (basePlace Q D)) (FiniteCompletion Q.L w) x) =
      algebraMap T.field (AlgebraicClosure T.field) (A.iso x) := by
  apply (intermediateClosureEquiv Q.F T).injective
  change intermediateClosureEquiv Q.F T ((intermediateClosureEquiv Q.F T).symm
    ((Q.Ps.isoTilde (FiniteExtension.completionMap (basePlace Q D) w x) :
      (galoisClosure Q.F Q.F').field) : AlgebraicClosure Q.F.Carrier)) = _
  rw [AlgEquiv.apply_symm_apply, intermediateClosureEquiv_algebraMap]
  exact (A.commutes x).symm

/-- The completed relative field in the child's own algebraic closure. -/
def localImage (B : IntermediateField D Q.L) :
    IntermediateField T.field (AlgebraicClosure T.field) :=
  MackeyCompletion.mapField A.iso (topEmbedding Q T) A.topEmbedding_commutes
    (MackeyCompletion.completedField (basePlace Q D) w B)

/-- The commuting isomorphism from the actual completion of a relative field. -/
def localEquiv (B : IntermediateField D Q.L) :
    FiniteCompletion B ((w).under (𝓞 B)) ≃+* A.localImage B :=
  letI := MackeyCompletion.under_liesOver (basePlace Q D) w B
  ((IsScalarTower.toAlgHom (FiniteCompletion D (basePlace Q D))
    (FiniteCompletion B ((w).under (𝓞 B))) (FiniteCompletion Q.L w)).equivFieldRange.toRingEquiv).trans
      (MackeyCompletion.mapFieldEquiv A.iso (topEmbedding Q T) A.topEmbedding_commutes
        (MackeyCompletion.completedField (basePlace Q D) w B))

theorem localEquiv_apply (B : IntermediateField D Q.L) (x : FiniteCompletion B ((w).under (𝓞 B))) :
    (A.localEquiv B x : AlgebraicClosure T.field) =
      topEmbedding Q T (FiniteExtension.completionMap ((w).under (𝓞 B)) w x) :=
  rfl

variable (a : Q.L ≃ₐ[Q.E] Q.L)

/-- The extension of the completed base induced by the actual compositum. -/
def localInducing : Extension (T.asPadicField (p := Q.p)) :=
  ⟨A.localImage (inducingField Q D a), by
    apply Module.finite_of_finrank_pos
    change 0 < Module.finrank T.field (MackeyCompletion.mapField A.iso (topEmbedding Q T)
      A.topEmbedding_commutes (MackeyCompletion.completedField (basePlace Q D) w (inducingField Q D a)))
    rw [← Algebra.finrank_eq_of_equiv_equiv A.iso
      (MackeyCompletion.mapFieldEquiv A.iso (topEmbedding Q T) A.topEmbedding_commutes
        (MackeyCompletion.completedField (basePlace Q D) w (inducingField Q D a)))
      (MackeyCompletion.mapFieldEquiv_commutes A.iso (topEmbedding Q T) A.topEmbedding_commutes _)]
    exact Module.finrank_pos⟩

theorem localClosure_eq [IsGalois Q.E Q.L] (h : HasUniquePlaceAbove Q.L Q.Ps.v) :
    A.localImage (closure Q D a) =
      (galoisClosure (T.asPadicField (p := Q.p)) (A.localInducing a)).field := by
  have : IsGalois D Q.L := IsGalois.tower_top_of_isGalois Q.E D Q.L
  have := isGalois_adicCompletion (basePlace Q D) w
  change MackeyCompletion.mapField A.iso (topEmbedding Q T) A.topEmbedding_commutes
      (MackeyCompletion.completedField (basePlace Q D) w
        (IntermediateField.normalClosure D (inducingField Q D a) Q.L)) = _
  rw [MackeyCompletion.completedField_normalClosure _ _
    (MackeyCompletion.uniqueAboveMiddle h (basePlace Q D)),
    MackeyCompletion.mapField_normalClosure]
  rfl

/-- The child's actual auxiliary places, with isomorphisms into its own closure. -/
def place [IsGalois Q.E Q.L] (h : HasUniquePlaceAbove Q.L Q.Ps.v) :
    PlaceDatum (T.asPadicField (p := Q.p)) (A.localInducing a)
      D (inducingField Q D a) (closure Q D a) where
  v := basePlace Q D
  v' := inducingPlace Q D a
  vTilde := closurePlace Q D a
  iso := A.iso
  isoTilde := (A.localEquiv (closure Q D a)).trans
    (IntermediateField.equivOfEq (A.localClosure_eq a h)).toRingEquiv

theorem place_isoTilde_apply [IsGalois Q.E Q.L] (h : HasUniquePlaceAbove Q.L Q.Ps.v)
    (x : FiniteCompletion (closure Q D a) (closurePlace Q D a)) :
    ((A.place a h).isoTilde x : AlgebraicClosure T.field) =
      topEmbedding Q T (FiniteExtension.completionMap (closurePlace Q D a) w x) :=
  A.localEquiv_apply _ x

theorem place_inducing_apply [IsGalois Q.E Q.L] (h : HasUniquePlaceAbove Q.L Q.Ps.v)
    (x : FiniteCompletion (inducingField Q D a) (inducingPlace Q D a)) :
    (((A.place a h).isoTilde (FiniteExtension.completionMap (A.place a h).v'
      (A.place a h).vTilde x) : (galoisClosure _ (A.localInducing a)).field) :
        AlgebraicClosure T.field) = (A.localEquiv (inducingField Q D a) x :
          AlgebraicClosure T.field) := by
  let y := FiniteExtension.completionMap (inducingPlace Q D a) (closurePlace Q D a) x
  calc
    _ = topEmbedding Q T (FiniteExtension.completionMap (closurePlace Q D a) w y) :=
      A.place_isoTilde_apply a h y
    _ = topEmbedding Q T (FiniteExtension.completionMap (inducingPlace Q D a) w x) :=
      congrArg (topEmbedding Q T) (DFunLike.congr_fun
        (CompletionTower.completionMap_comp (inducingPlace Q D a) (closurePlace Q D a) w) x)
    _ = _ := (A.localEquiv_apply (inducingField Q D a) x).symm

theorem place_compatible [IsGalois Q.E Q.L] (h : HasUniquePlaceAbove Q.L Q.Ps.v) :
    (A.place a h).IsCompatible := by
  constructor
  · intro x
    apply Subtype.ext
    let y := FiniteExtension.completionMap (basePlace Q D) (closurePlace Q D a) x
    calc
      _ = topEmbedding Q T (FiniteExtension.completionMap (closurePlace Q D a) w y) :=
        A.place_isoTilde_apply a h y
      _ = topEmbedding Q T (FiniteExtension.completionMap (basePlace Q D) w x) :=
        congrArg (topEmbedding Q T) (DFunLike.congr_fun
          (CompletionTower.completionMap_comp (basePlace Q D) (closurePlace Q D a) w) x)
      _ = algebraMap T.field (AlgebraicClosure T.field) (A.iso x) :=
        A.topEmbedding_commutes x
  · apply Set.Subset.antisymm
    · rintro _ ⟨x, rfl⟩
      exact Eq.mpr (congrArg (fun z : AlgebraicClosure T.field ↦ z ∈ (A.localInducing a).field)
        (A.place_inducing_apply a h x)) (A.localEquiv (inducingField Q D a) x).2
    · intro x hx
      obtain ⟨y, hy⟩ := (A.localEquiv (inducingField Q D a)).surjective ⟨x, hx⟩
      exact ⟨y, (A.place_inducing_apply a h y).trans (congrArg Subtype.val hy)⟩

end CompletedBase
end Langlands.Global.Harris.MackeyChild
