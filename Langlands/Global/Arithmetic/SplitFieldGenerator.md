# Splitting of a generating polynomial at finite and real places

Let \(F/E\) be a field extension generated as an algebra by an element \(b\) that is a root of a nonzero polynomial \(f\) over \(E\). For number fields, `completionEquivOfSplitGenerator` identifies the actual completion \(F_q\) with \(E_p\) through the completion embedding when \(q\) lies over \(p\) and \(f\) splits over \(E_p\). The field universes are independent.

The image of \(b\) in \(F_q\) is a root of the polynomial obtained from \(f\) by coefficient extension. It must belong to the image of \(E_p\) since the polynomial already splits there. Every element of \(F\) is a polynomial in \(b\) with coefficients in \(E\), so the image of \(F\) lies in the image of \(E_p\). The former image is dense and the latter is closed, which makes the completion embedding surjective.

`totallyReal_of_splitGenerator` assumes \(E\) is totally real and \(f\) splits over the reals at every real embedding of \(E\). A complex embedding of \(F\) restricts to a real embedding of \(E\). Its value on \(b\) is real by the split polynomial, and polynomial evaluation makes the whole image real. Thus every infinite place of \(F\) is real.
