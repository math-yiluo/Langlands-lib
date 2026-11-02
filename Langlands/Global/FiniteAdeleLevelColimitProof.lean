import Langlands.Global.FiniteAdeleLevelColimitStatement
import Langlands.Global.FiniteAdeleLevelTopologyProof

/-! # Categorical colimit proof for actual finite-adelic level rings -/

noncomputable section

universe u

open IsDedekindDomain CategoryTheory Limits

namespace Langlands.Global

namespace SubringCover

variable {ι A B : Type u} [CommRing A] [CommRing B]
variable (L : Finset ι → Subring A) (hL : Monotone L)
variable (hcover : ∀ a : A, ∃ S, a ∈ L S)
variable (f : ∀ S, L S →+* B)
variable (hf : ∀ (S T : Finset ι) (hST : S ⊆ T),
  (f T).comp (Subring.inclusion (hL hST)) = f S)

/-- Evaluate at a chosen level; the compatibility lemma removes the choice. -/
def descFun (a : A) : B :=
  f (hcover a).choose ⟨a, (hcover a).choose_spec⟩

include hL hf

theorem descFun_apply (S : Finset ι) (a : L S) :
    descFun L hcover f a.val = f S a := by
  classical
  let T := (hcover a.val).choose
  let b : L T := ⟨a.val, (hcover a.val).choose_spec⟩
  have hS := DFunLike.congr_fun (hf S (S ∪ T) Finset.subset_union_left) a
  have hT := DFunLike.congr_fun (hf T (S ∪ T) Finset.subset_union_right) b
  change f T b = f S a
  exact hT.symm.trans hS

/-- The ring homomorphism induced by a compatible family on a directed subring cover. -/
def desc : A →+* B where
  toFun := descFun L hcover f
  map_one' := by
    rw [← (L ∅).coe_one, descFun_apply L hL hcover f hf]
    exact map_one (f ∅)
  map_mul' a b := by
    classical
    obtain ⟨S, ha⟩ := hcover a
    obtain ⟨T, hb⟩ := hcover b
    let a' : L (S ∪ T) := ⟨a, hL Finset.subset_union_left ha⟩
    let b' : L (S ∪ T) := ⟨b, hL Finset.subset_union_right hb⟩
    change descFun L hcover f (a' * b').val =
      descFun L hcover f a'.val * descFun L hcover f b'.val
    rw [descFun_apply L hL hcover f hf, descFun_apply L hL hcover f hf,
      descFun_apply L hL hcover f hf]
    exact map_mul (f (S ∪ T)) a' b'
  map_zero' := by
    rw [← (L ∅).coe_zero, descFun_apply L hL hcover f hf]
    exact map_zero (f ∅)
  map_add' a b := by
    classical
    obtain ⟨S, ha⟩ := hcover a
    obtain ⟨T, hb⟩ := hcover b
    let a' : L (S ∪ T) := ⟨a, hL Finset.subset_union_left ha⟩
    let b' : L (S ∪ T) := ⟨b, hL Finset.subset_union_right hb⟩
    change descFun L hcover f (a' + b').val =
      descFun L hcover f a'.val + descFun L hcover f b'.val
    rw [descFun_apply L hL hcover f hf, descFun_apply L hL hcover f hf,
      descFun_apply L hL hcover f hf]
    exact map_add (f (S ∪ T)) a' b'

theorem desc_apply (S : Finset ι) (a : L S) :
    desc L hL hcover f hf a.val = f S a :=
  descFun_apply L hL hcover f hf S a

end SubringCover

variable (R K : Type u) [CommRing R] [IsDedekindDomain R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

def finiteAdeleLevelRingDesc (c : Cocone (finiteAdeleLevelRingDiagram R K)) :
    FiniteAdeleRing R K →+* c.pt :=
  SubringCover.desc (B := c.pt) (finiteAdeleLevel R K)
    (fun _ _ h => finiteAdeleLevel_mono R K h)
    (exists_mem_finiteAdeleLevel R K) (fun S => (c.ι.app S).hom)
    (fun _S _T h => congrArg CommRingCat.Hom.hom (c.w (homOfLE h)))

theorem finiteAdeleLevelRingDesc_apply (c : Cocone (finiteAdeleLevelRingDiagram R K))
    (S : Finset (HeightOneSpectrum R)) (a : finiteAdeleLevel R K S) :
    finiteAdeleLevelRingDesc R K c a.val = (c.ι.app S).hom a :=
  SubringCover.desc_apply _ _ _ _ _ S a

def finiteAdeleLevelRingIsColimit : IsColimit (finiteAdeleLevelRingCocone R K) where
  desc c := CommRingCat.ofHom (finiteAdeleLevelRingDesc R K c)
  fac c S := by
    ext a
    exact finiteAdeleLevelRingDesc_apply R K c S a
  uniq c m hm := by
    ext a
    obtain ⟨S, ha⟩ := exists_mem_finiteAdeleLevel R K a
    have h := congrArg (fun k => k.hom ⟨a, ha⟩) (hm S)
    exact h.trans (finiteAdeleLevelRingDesc_apply R K c S ⟨a, ha⟩).symm

def finiteAdeleLevelIsColimit : IsColimit (finiteAdeleLevelCocone R K) where
  desc c := by
    let f : FiniteAdeleRing R K →+* c.pt :=
      finiteAdeleLevelRingDesc R K ((forget₂ TopCommRingCat CommRingCat).mapCocone c)
    refine ⟨f, ?_⟩
    apply (continuous_iff_finiteAdeleLevel R K (X := c.pt) f).mpr
    intro S
    have heq : (f ∘ (finiteAdeleLevel R K S).subtype) =
        (c.ι.app S).val := by
      funext a
      exact finiteAdeleLevelRingDesc_apply R K _ S a
    exact heq.symm ▸ (c.ι.app S).property
  fac c S := by
    apply Subtype.ext
    ext a
    exact finiteAdeleLevelRingDesc_apply R K _ S a
  uniq c m hm := by
    apply Subtype.ext
    ext a
    obtain ⟨S, ha⟩ := exists_mem_finiteAdeleLevel R K a
    have h := congrArg (fun k => k.val ⟨a, ha⟩) (hm S)
    exact h.trans (finiteAdeleLevelRingDesc_apply R K
      ((forget₂ TopCommRingCat CommRingCat).mapCocone c) S ⟨a, ha⟩).symm

/-- Both exact categorical universal properties of the canonical level cocones. -/
theorem finiteAdeleLevelColimit : FiniteAdeleLevelColimitStatement.{u} := by
  intro R K _ _ _ _ _
  exact ⟨⟨finiteAdeleLevelIsColimit R K⟩, ⟨finiteAdeleLevelRingIsColimit R K⟩⟩

end Langlands.Global
