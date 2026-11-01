import Langlands.AlgebraicGeometry.Modules.CommonSourceCocycle
import Langlands.AlgebraicGeometry.Modules.PullbackTransport
import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesZariskiSeparatedProof

/-! # Transporting common-source overlap identifications -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Langlands.Scheme.Modules.CommonSourceCocycle

open Langlands.SchemeModule.RigidifiedModule

/-- Naturality of a specified-composite comparison. -/
lemma compHom_naturality {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (h : A ⟶ C)
    (w : f ≫ g = h) {M N : C.Modules} (k : M ⟶ N) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map k) ≫
        compHom f g h w N =
      compHom f g h w M ≫ (Scheme.Modules.pullback h).map k :=
  (Langlands.Scheme.Modules.compHom_naturality f g h w k).symm

/-- Normalize a pullback of a piece identified with a common module. -/
def pieceComp {V U X : Scheme.{u}} (f : V ⟶ U) (a : U ⟶ X)
    (z : V ⟶ X) (h : f ≫ a = z) (N : X.Modules) {M : U.Modules}
    (e : (Scheme.Modules.pullback a).obj N ≅ M) :
    (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback z).obj N :=
  (Scheme.Modules.pullback f).map e.inv ≫ compHom f a z h N

instance pieceComp_isIso {V U X : Scheme.{u}} (f : V ⟶ U) (a : U ⟶ X)
    (z : V ⟶ X) (h : f ≫ a = z) (N : X.Modules) {M : U.Modules}
    (e : (Scheme.Modules.pullback a).obj N ≅ M) : IsIso (pieceComp f a z h N e) := by
  unfold pieceComp compHom
  infer_instance

/-- A transported transition preserves the twofold normalization. -/
lemma transition_pieceComp {V A B X : Scheme.{u}} (f : V ⟶ A) (g : V ⟶ B)
    (a : A ⟶ X) (b : B ⟶ X) (h : f ≫ a = g ≫ b) (N : X.Modules)
    {Ma : A.Modules} {Mb : B.Modules}
    (ea : (Scheme.Modules.pullback a).obj N ≅ Ma)
    (eb : (Scheme.Modules.pullback b).obj N ≅ Mb)
    (z : V ⟶ X) (ha : f ≫ a = z) (hb : g ≫ b = z) :
    (transition f g a b h N ea eb).hom ≫ pieceComp g b z hb N eb =
      pieceComp f a z ha N ea := by
  simp only [transition, pieceComp, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Category.assoc]
  rw [← Functor.map_comp_assoc (Scheme.Modules.pullback g) eb.hom,
    Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp,
    square_normalize b f g a h N z hb]

/-- Composing a piece normalization is the threefold normalization. -/
lemma compHom_pieceComp {W V U X : Scheme.{u}} (t : W ⟶ V) (f : V ⟶ U)
    (a : U ⟶ X) (f' : W ⟶ U) (hf : t ≫ f = f') (N : X.Modules)
    {M : U.Modules} (e : (Scheme.Modules.pullback a).obj N ≅ M)
    (z : W ⟶ X) (ha : f' ≫ a = z) (hz : t ≫ (f ≫ a) = z) :
    compHom t f f' hf M ≫ pieceComp f' a z ha N e =
      pieceNormalize t f a z hz N e := by
  simp only [pieceComp, pieceNormalize]
  rw [← reassoc_of% (compHom_naturality t f f' hf e.inv)]
  congr 1
  exact compHom_assoc t f a f' (f ≫ a) z hf rfl ha hz N

/-- Pull an overlap identification along a map with prescribed projection composites. -/
def transport {W V A B : Scheme.{u}} (t : W ⟶ V) (f : V ⟶ A) (g : V ⟶ B)
    (f' : W ⟶ A) (g' : W ⟶ B) (hf : t ≫ f = f') (hg : t ≫ g = g')
    {Ma : A.Modules} {Mb : B.Modules}
    (φ : (Scheme.Modules.pullback f).obj Ma ≅ (Scheme.Modules.pullback g).obj Mb) :
    (Scheme.Modules.pullback f').obj Ma ≅ (Scheme.Modules.pullback g').obj Mb :=
  (Langlands.Scheme.Modules.compIso t f f' hf Ma).symm ≪≫
    (Scheme.Modules.pullback t).mapIso φ ≪≫
      Langlands.Scheme.Modules.compIso t g g' hg Mb

/-- Transporting a common-source transition gives exactly the induced transition. -/
lemma transport_transition {W V A B X : Scheme.{u}}
    (t : W ⟶ V) (f : V ⟶ A) (g : V ⟶ B) (f' : W ⟶ A) (g' : W ⟶ B)
    (hf : t ≫ f = f') (hg : t ≫ g = g') (a : A ⟶ X) (b : B ⟶ X)
    (h : f ≫ a = g ≫ b) (h' : f' ≫ a = g' ≫ b) (N : X.Modules)
    {Ma : A.Modules} {Mb : B.Modules}
    (ea : (Scheme.Modules.pullback a).obj N ≅ Ma)
    (eb : (Scheme.Modules.pullback b).obj N ≅ Mb) :
    transport t f g f' g' hf hg (transition f g a b h N ea eb) =
      transition f' g' a b h' N ea eb := by
  ext1
  rw [← cancel_epi (compHom t f f' hf Ma)]
  change (Langlands.Scheme.Modules.compIso t f f' hf Ma).hom ≫ _ =
    (Langlands.Scheme.Modules.compIso t f f' hf Ma).hom ≫ _
  simp only [transport, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.hom_inv_id_assoc]
  change (Scheme.Modules.pullback t).map (transition f g a b h N ea eb).hom ≫
      compHom t g g' hg Mb =
    compHom t f f' hf Ma ≫ (transition f' g' a b h' N ea eb).hom
  rw [← cancel_mono (pieceComp g' b (g' ≫ b) rfl N eb)]
  simp only [Category.assoc]
  have ha : t ≫ (f ≫ a) = g' ≫ b := by rw [← Category.assoc, hf, h']
  have hb : t ≫ (g ≫ b) = g' ≫ b := by rw [← Category.assoc, hg]
  rw [compHom_pieceComp t g b g' hg N eb _ rfl hb,
    inner_transition_normalize t f g a b h N ea eb _ ha hb,
    transition_pieceComp f' g' a b h' N ea eb _ h' rfl,
    compHom_pieceComp t f a f' hf N ea _ h' ha]

/-- Transport along a scheme isomorphism retains the actual overlap identification. -/
lemma transport_injective {W V A B : Scheme.{u}} (t : W ⟶ V) [IsIso t]
    (f : V ⟶ A) (g : V ⟶ B) (f' : W ⟶ A) (g' : W ⟶ B)
    (hf : t ≫ f = f') (hg : t ≫ g = g') {Ma : A.Modules} {Mb : B.Modules} :
    Function.Injective (transport t f g f' g' hf hg (Ma := Ma) (Mb := Mb)) := by
  intro φ ψ h
  apply Iso.ext
  apply Langlands.Scheme.Modules.pullback_map_injective_of_iso (asIso t)
  change (Scheme.Modules.pullback t).map φ.hom =
    (Scheme.Modules.pullback t).map ψ.hom
  apply (cancel_epi (Langlands.Scheme.Modules.compIso t f f' hf Ma).inv).1
  apply (cancel_mono (Langlands.Scheme.Modules.compIso t g g' hg Mb).hom).1
  simpa only [transport, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc] using congrArg Iso.hom h

/-- A piece comparison induced from a pullback of a larger common source. -/
def sourceComparison {U X Y : Scheme.{u}} (a : U ⟶ X) (h : X ⟶ Y)
    (N : X.Modules) (K : Y.Modules) (e : (Scheme.Modules.pullback h).obj K ≅ N)
    {M : U.Modules} (ea : (Scheme.Modules.pullback a).obj N ≅ M) :
    (Scheme.Modules.pullback (a ≫ h)).obj K ≅ M :=
  (Langlands.Scheme.Modules.compIso a h (a ≫ h) rfl K).symm ≪≫
    (Scheme.Modules.pullback a).mapIso e ≪≫ ea

/-- Changing the common source commutes with the twofold normalization. -/
lemma pieceComp_changeSource {V U X Y : Scheme.{u}} (f : V ⟶ U) (a : U ⟶ X)
    (h : X ⟶ Y) (z : V ⟶ X) (hf : f ≫ a = z) (w : V ⟶ Y)
    (hz : z ≫ h = w) (hw : f ≫ (a ≫ h) = w) (N : X.Modules) (K : Y.Modules)
    (e : (Scheme.Modules.pullback h).obj K ≅ N) {M : U.Modules}
    (ea : (Scheme.Modules.pullback a).obj N ≅ M) :
    pieceComp f (a ≫ h) w hw K (sourceComparison a h N K e ea) =
      pieceComp f a z hf N ea ≫ (Scheme.Modules.pullback z).map e.inv ≫
        compHom z h w hz K := by
  simp only [pieceComp, sourceComparison, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv, Functor.map_comp, Category.assoc]
  change (Scheme.Modules.pullback f).map ea.inv ≫
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback a).map e.inv) ≫
      (Scheme.Modules.pullback f).map (compHom a h (a ≫ h) rfl K) ≫
      compHom f (a ≫ h) w hw K = _
  rw [← compHom_assoc f a h z (a ≫ h) w hf rfl hz hw K,
    reassoc_of% (compHom_naturality f a z hf e.inv)]

/-- Replacing a common source by a module whose pullback is identified with it
preserves the actual transitions, with the induced piece comparisons. -/
lemma transition_changeSource {V A B X Y : Scheme.{u}}
    (f : V ⟶ A) (g : V ⟶ B) (a : A ⟶ X) (b : B ⟶ X)
    (hab : f ≫ a = g ≫ b) (h : X ⟶ Y)
    (hab' : f ≫ (a ≫ h) = g ≫ (b ≫ h)) (N : X.Modules) (K : Y.Modules)
    (e : (Scheme.Modules.pullback h).obj K ≅ N) {Ma : A.Modules} {Mb : B.Modules}
    (ea : (Scheme.Modules.pullback a).obj N ≅ Ma)
    (eb : (Scheme.Modules.pullback b).obj N ≅ Mb) :
    transition f g (a ≫ h) (b ≫ h) hab' K
        (sourceComparison a h N K e ea) (sourceComparison b h N K e eb) =
      transition f g a b hab N ea eb := by
  ext1
  rw [← cancel_mono (pieceComp g (b ≫ h) (g ≫ (b ≫ h)) rfl K
    (sourceComparison b h N K e eb))]
  rw [transition_pieceComp f g (a ≫ h) (b ≫ h) hab' K _ _ _ hab' rfl]
  have hz : (g ≫ b) ≫ h = g ≫ (b ≫ h) := Category.assoc _ _ _
  rw [pieceComp_changeSource f a h (g ≫ b) hab _ hz hab' N K e ea,
    pieceComp_changeSource g b h (g ≫ b) rfl _ hz rfl N K e eb]
  rw [reassoc_of% (transition_pieceComp f g a b hab N ea eb _ hab rfl)]

end Langlands.Scheme.Modules.CommonSourceCocycle
