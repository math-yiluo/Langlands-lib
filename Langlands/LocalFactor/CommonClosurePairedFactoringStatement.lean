import Langlands.LocalFactor.CommonClosureFactoringBrauer
import Langlands.Weil.Local.ExtensionWeil

/-! # A common finite Galois bound for two Weil factoring kernels -/

set_option autoImplicit false

universe uF uE uQ uR

namespace Langlands.LocalFactor.CommonClosure

open Weil.Local

/-- Given an embedding of \(p\)-adic fields and a finite factoring map on each
side, there is a finite Galois extension of the base containing the image of
the top field. Its Weil subgroup and its inverse image under the Weil map are
contained in the corresponding closed factoring kernels. -/
def PairedFactoringGaloisBoundStatement : Prop :=
  ∀ {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (E : PadicField.{uE} p)
    (f : F.Carrier →ₐ[Padic p] E.Carrier)
    {Q : Type uQ} [Group Q] [Finite Q] {R : Type uR} [Group R] [Finite R]
    (qF : Field.absoluteGaloisGroup F.Carrier →* Q)
    (qE : Field.absoluteGaloisGroup E.Carrier →* R),
    ∃ N : Extension F, IsGalois F.Carrier N.field ∧
      extensionIntermediateField F E f ≤ N.field ∧
      weilSubgroup F N ≤ factoringKernelClosure F qF ∧
      (weilSubgroup F N).comap (extensionWeilMap F E f).toMonoidHom ≤
        factoringKernelClosure E qE

end Langlands.LocalFactor.CommonClosure
